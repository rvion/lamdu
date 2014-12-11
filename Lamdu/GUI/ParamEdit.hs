module Lamdu.GUI.ParamEdit
  ( make
  ) where

import Control.Lens.Operators
import Control.MonadA (MonadA)
import Data.Monoid (Monoid(..))
import Lamdu.GUI.ExpressionGui (ExpressionGui)
import Lamdu.GUI.ExpressionGui.Monad (ExprGuiM, WidgetT)
import Lamdu.Sugar.AddNames.Types (Name(..))
import System.Random.Utils (genFromHashable)
import qualified Graphics.UI.Bottle.EventMap as E
import qualified Graphics.UI.Bottle.Widget as Widget
import qualified Graphics.UI.Bottle.Widgets.FocusDelegator as FocusDelegator
import qualified Lamdu.Config as Config
import qualified Lamdu.GUI.ExpressionGui as ExpressionGui
import qualified Lamdu.GUI.ExpressionGui.Monad as ExprGuiM
import qualified Lamdu.GUI.TypeView as TypeView
import qualified Lamdu.GUI.WidgetEnvT as WE
import qualified Lamdu.GUI.WidgetIds as WidgetIds
import qualified Lamdu.Sugar.Types as Sugar

paramFDConfig :: FocusDelegator.Config
paramFDConfig = FocusDelegator.Config
  { FocusDelegator.startDelegatingKeys = [E.ModKey E.noMods E.Key'Enter]
  , FocusDelegator.startDelegatingDoc = E.Doc ["Edit", "Rename parameter"]
  , FocusDelegator.stopDelegatingKeys = [E.ModKey E.noMods E.Key'Escape]
  , FocusDelegator.stopDelegatingDoc = E.Doc ["Edit", "Done renaming"]
  }

makeParamNameEdit ::
  MonadA m => Name m -> Widget.Id -> ExprGuiM m (WidgetT m)
makeParamNameEdit nameProp myId = do
  config <- ExprGuiM.widgetEnv WE.readConfig
  ExprGuiM.wrapDelegated paramFDConfig FocusDelegator.NotDelegating id
    (ExprGuiM.withFgColor (Config.paramOriginColor config) .
     ExpressionGui.makeNameEdit nameProp) myId

-- exported for use in definition sugaring.
make ::
  MonadA m => ExprGuiM.ShowType -> Widget.Id ->
  Sugar.FuncParam (Name m) m ->
  ExprGuiM m (ExpressionGui m)
make showType prevId param =
  assignCursor $ do
    config <- ExprGuiM.widgetEnv WE.readConfig
    let
      paramAddNextEventMap =
        maybe mempty
        (Widget.keysEventMapMovesCursor (Config.addNextParamKeys config)
         (E.Doc ["Edit", "Add next parameter"]) .
         fmap (FocusDelegator.delegatingId . WidgetIds.fromEntityId) .
         (^. Sugar.fpListItemActions . Sugar.itemAddNext))
        mActions
      paramEventMap = mconcat
        [ paramDeleteEventMap (Config.delForwardKeys config) "" id
        , paramDeleteEventMap (Config.delBackwardKeys config) " backwards" (const prevId)
        , paramAddNextEventMap
        ]
    paramNameEdit <-
      makeParamNameEdit (param ^. Sugar.fpName) myId
      <&> Widget.weakerEvents paramEventMap
      <&> ExpressionGui.fromValueWidget
    s <- ExprGuiM.shouldShowType showType
    if s
      then do
        paramTypeView <-
          param ^. Sugar.fpInferredType
          & TypeView.make (genFromHashable entityId)
          & ExprGuiM.widgetEnv
          <&> uncurry Widget.liftView
        return $
          ExpressionGui.addType config ExpressionGui.Background myId
          paramTypeView paramNameEdit
      else
        return paramNameEdit
  where
    entityId = param ^. Sugar.fpId
    myId = WidgetIds.fromEntityId entityId
    mActions = param ^. Sugar.fpMActions
    hiddenIds = map WidgetIds.fromEntityId $ param ^. Sugar.fpHiddenIds
    assignCursor x =
      foldr (`ExprGuiM.assignCursorPrefix` myId) x hiddenIds
    paramDeleteEventMap keys docSuffix onId =
      maybe mempty
      (Widget.keysEventMapMovesCursor keys (E.Doc ["Edit", "Delete parameter" ++ docSuffix]) .
       fmap (onId . WidgetIds.fromEntityId) .
       (^. Sugar.fpListItemActions . Sugar.itemDelete))
      mActions
