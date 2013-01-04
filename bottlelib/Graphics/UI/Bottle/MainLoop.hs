{-# LANGUAGE TemplateHaskell, CPP #-}
module Graphics.UI.Bottle.MainLoop
  ( mainLoopAnim
  , mainLoopImage
  , mainLoopWidget
  ) where

import           Control.Applicative ((<$>), (<*>))
import           Control.Concurrent (threadDelay)
import           Control.Concurrent.MVar
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Lens.Tuple
import           Control.Monad (when, unless)
import qualified Data.ByteString.Char8 as SBS8
import           Data.IORef
import           Data.List (genericLength)
import           Data.MRUMemo (memoIO)
import           Data.Monoid (Monoid(..), (<>))
import qualified Data.Monoid as Monoid
import           Data.Time.Clock (NominalDiffTime)
import           Data.Time.Clock (getCurrentTime, diffUTCTime)
import           Data.Traversable (traverse, sequenceA)
import           Data.Vector.Vector2 (Vector2(..))
import           Graphics.DrawingCombinators ((%%))
import qualified Graphics.DrawingCombinators as Draw
import           Graphics.DrawingCombinators.Utils (Image)
import qualified Graphics.DrawingCombinators.Utils as DrawUtils
import           Graphics.Rendering.OpenGL.GL (($=))
import qualified Graphics.Rendering.OpenGL.GL as GL
import           Graphics.UI.Bottle.Animation (AnimId)
import qualified Graphics.UI.Bottle.Animation as Anim
import qualified Graphics.UI.Bottle.EventMap as E
import           Graphics.UI.Bottle.SizedFont (SizedFont(..))
import qualified Graphics.UI.Bottle.SizedFont as SizedFont
import           Graphics.UI.Bottle.View (View(..))
import qualified Graphics.UI.Bottle.View as View
import           Graphics.UI.Bottle.Widget (Widget)
import qualified Graphics.UI.Bottle.Widget as Widget
import qualified Graphics.UI.Bottle.Widgets.GridView as GridView
import qualified Graphics.UI.GLFW as GLFW
import           Graphics.UI.GLFW.Events (KeyEvent, Event(..), eventLoop)
import           Text.Printf.Mauke.TH

timeBetweenInvocations :: IO ((Maybe NominalDiffTime -> IO a) -> IO a)
timeBetweenInvocations = do
  mLastInvocationTimeVar <- newMVar Nothing
  return $ modifyMVar mLastInvocationTimeVar . updateTime
  where
    updateTime f mLastInvocationTime = do
      currentTime <- getCurrentTime
      let
        mTimeSince =
          fmap (currentTime `diffUTCTime`) mLastInvocationTime
      result <- f mTimeSince
      return (Just currentTime, result)

mkStatser :: (Ord a, Fractional a) => Int -> IO (a -> IO (a, a, a))
mkStatser n = do
  fifo <- newIORef []
  return $ \added -> do
    modifyIORef fifo (take n . (added:))
    samples <- readIORef fifo
    return (minimum samples, avg samples, maximum samples)
  where
    avg = (/) <$> sum <*> genericLength

placeAt :: Widget.Size -> Vector2 Widget.R -> View -> View
placeAt winSize ratio view =
  view
  & View.animFrame %~ Anim.translate (ratio * (winSize - view ^. View.size))

renderText :: SizedFont -> Int -> String -> View
renderText fpsFont i text =
  View size (Anim.sizedFrame [SBS8.pack (show i)] size image)
  where
    image = SizedFont.render fpsFont text
    size = SizedFont.textSize fpsFont text

mainLoopImage ::
  GLFW.Window -> Draw.Font -> (Widget.Size -> KeyEvent -> IO Bool) ->
  (Bool -> Widget.Size -> IO (Maybe Image)) -> IO a
mainLoopImage win font eventHandler makeImage =
  do
    statser <- mkStatser 20
    addDelayArg <- timeBetweenInvocations
    eventLoop win $ handleEvents statser addDelayArg
  where
    windowSize = do
      (x, y) <- GLFW.getFramebufferSize win
      return $ fromIntegral <$> Vector2 x y

    handleEvent size (EventKey keyEvent) =
      eventHandler size keyEvent
    handleEvent _ EventWindowClose =
      error "Quit" -- TODO: Make close event
    handleEvent _ EventWindowRefresh = return True

    fpsFont = SizedFont font 20
    addDelayToImage statser winSize mkMImage mTimeSince = do
      mImage <- mkMImage
      let
        right = Vector2 1 0
        mkFpsImage (lo, avg, hi) =
          [lo, avg, hi]
          <&> $(printf "%02.02f")
          & zipWith (renderText fpsFont) [0..]
          <&> (: [])
          & GridView.makeAlign right
          & placeAt winSize (Vector2 1 0)
      fpsImage <-
        mTimeSince
        & maybe (return View.empty) (fmap mkFpsImage . statser . (1/))
      mImage
        <&> mappend (Anim.draw (fpsImage ^. View.animFrame))
        & return

    handleEvents statser addDelayArg events = do
      winSize@(Vector2 winSizeX winSizeY) <- windowSize
      anyChange <- or <$> traverse (handleEvent winSize) events
      -- TODO: Don't do this *EVERY* frame but on frame-buffer size update events?
      GL.viewport $=
        (GL.Position 0 0,
         GL.Size (round winSizeX) (round winSizeY))
      mNewImage <-
        makeImage anyChange winSize
        & addDelayToImage statser winSize
        & addDelayArg
      case mNewImage of
        Nothing ->
          -- TODO: If we can verify that there's sync-to-vblank, we
          -- need no sleep here
          threadDelay 10000
        Just image ->
          image
          & (DrawUtils.translate (Vector2 (-1) 1) <> DrawUtils.scale (Vector2 (2/winSizeX) (-2/winSizeY)) %%)
#ifdef DRAWINGCOMBINATORS__SIZED
          & let Vector2 glPixelRatioX glPixelRatioY = winSize / 2 -- GL range is -1..1
            in Draw.clearRenderSized (glPixelRatioX, glPixelRatioY)
#else
          & Draw.clearRender
#endif

mainLoopAnim ::
  GLFW.Window -> Draw.Font ->
  (Widget.Size -> IO (Maybe (Monoid.Endo AnimId))) ->
  (Widget.Size -> KeyEvent -> IO (Maybe (Monoid.Endo AnimId))) ->
  (Widget.Size -> IO Anim.Frame) ->
  IO Anim.R -> IO a
mainLoopAnim win font tickHandler eventHandler makeFrame getAnimationHalfLife = do
  frameStateVar <- newIORef Nothing
  let
    handleResult Nothing = return False
    handleResult (Just animIdMapping) = do
      modifyIORef frameStateVar . fmap $
        (_1 .~  0) .
        (_2 . _2 %~ Anim.mapIdentities (Monoid.appEndo animIdMapping))
      return True

    nextFrameState curTime size Nothing = do
      dest <- makeFrame size
      return $ Just (0, (curTime, dest))
    nextFrameState curTime size (Just (drawCount, (prevTime, prevFrame))) =
      if drawCount == 0
      then do
        dest <- makeFrame size
        animationHalfLife <- getAnimationHalfLife
        let
          elapsed = realToFrac (curTime `diffUTCTime` prevTime)
          progress = 1 - 0.5 ** (elapsed/animationHalfLife)
        return . Just $
          case Anim.nextFrame progress dest prevFrame of
            Nothing -> (drawCount + 1, (curTime, dest))
            Just newFrame -> (0 :: Int, (curTime, newFrame))
      else
        return $ Just (drawCount + 1, (curTime, prevFrame))

    makeImage forceRedraw size = do
      when forceRedraw .
        modifyIORef frameStateVar $
        Lens.mapped . _1 .~ 0
      _ <- handleResult =<< tickHandler size
      curTime <- getCurrentTime
      writeIORef frameStateVar =<<
        nextFrameState curTime size =<< readIORef frameStateVar
      frameStateResult <$> readIORef frameStateVar

    frameStateResult Nothing = error "No frame to draw at start??"
    frameStateResult (Just (drawCount, (_, frame)))
      | drawCount < stopAtDrawCount = Just $ Anim.draw frame
      | otherwise = Nothing
    -- A note on draw counts:
    -- When a frame is dis-similar to the previous the count resets to 0
    -- When a frame is similar and animation stops the count becomes 1
    -- We then should draw it again (for double buffering issues) at count 2
    -- And stop drawing it at count 3.
    stopAtDrawCount = 3
    imgEventHandler size event =
      handleResult =<< eventHandler size event
  mainLoopImage win font imgEventHandler makeImage

mainLoopWidget :: GLFW.Window -> IO Bool -> Draw.Font -> (Widget.Size -> IO (Widget IO)) -> IO Anim.R -> IO a
mainLoopWidget win widgetTickHandler font mkWidgetUnmemod getAnimationHalfLife = do
  mkWidgetRef <- newIORef =<< memoIO mkWidgetUnmemod
  let
    newWidget = writeIORef mkWidgetRef =<< memoIO mkWidgetUnmemod
    getWidget size = ($ size) =<< readIORef mkWidgetRef
    tickHandler size = do
      anyUpdate <- widgetTickHandler
      when anyUpdate newWidget
      widget <- getWidget size
      tickResults <-
        sequenceA (widget ^. Widget.eventMap . E.emTickHandlers)
      unless (null tickResults) newWidget
      return $
        case (tickResults, anyUpdate) of
        ([], False) -> Nothing
        _ -> Just . mconcat $ map (^. Widget.eAnimIdMapping) tickResults
    eventHandler size event = do
      widget <- getWidget size
      mAnimIdMapping <-
        (traverse . fmap) (^. Widget.eAnimIdMapping) .
        E.lookup event $ widget ^. Widget.eventMap
      case mAnimIdMapping of
        Nothing -> return ()
        Just _ -> newWidget
      return mAnimIdMapping
    mkFrame size = getWidget size <&> (^. Widget.animFrame)
  mainLoopAnim win font tickHandler eventHandler mkFrame getAnimationHalfLife
