{-# OPTIONS -fno-warn-orphans #-}
{-# LANGUAGE TemplateHaskell #-}
module Lamdu.Config (Config(..), delKeys) where

import Data.Aeson (ToJSON(..), FromJSON(..))
import Data.Aeson.TH (deriveJSON)
import Data.Vector.Vector2 (Vector2(..))
import Foreign.C.Types (CDouble)
import Graphics.DrawingCombinators.Utils () -- Read instance for Color
import qualified Graphics.DrawingCombinators as Draw
import qualified Graphics.UI.Bottle.EventMap as E

data Config = Config
  { baseColor :: Draw.Color
  , baseTextSize :: Int
  , helpTextColor :: Draw.Color
  , helpTextSize :: Int
  , helpInputDocColor :: Draw.Color
  , helpBGColor :: Draw.Color

  , quitKeys :: [E.ModKey]
  , undoKeys :: [E.ModKey]
  , redoKeys :: [E.ModKey]
  , makeBranchKeys :: [E.ModKey]

  , jumpToBranchesKeys :: [E.ModKey]

  , overlayDocKeys :: [E.ModKey]

  , addNextParamKeys :: [E.ModKey]

  , delBranchKeys :: [E.ModKey]

  , closePaneKeys :: [E.ModKey]
  , movePaneDownKeys :: [E.ModKey]
  , movePaneUpKeys :: [E.ModKey]

  , replaceKeys :: [E.ModKey]

  , pickResultKeys :: [E.ModKey]
  , pickAndMoveToNextHoleKeys :: [E.ModKey]

  , jumpToDefinitionKeys :: [E.ModKey]

  , delForwardKeys :: [E.ModKey]
  , delBackwardKeys :: [E.ModKey]
  , wrapKeys :: [E.ModKey]
  , debugModeKeys :: [E.ModKey]

  , newDefinitionKeys :: [E.ModKey]

  , definitionColor :: Draw.Color
  , atomColor :: Draw.Color
  , parameterColor :: Draw.Color
  , paramOriginColor :: Draw.Color

  , literalIntColor :: Draw.Color

  , previousCursorKeys :: [E.ModKey]

  , holeResultCount :: Int
  , holeResultScaleFactor :: Vector2 Double
  , holeResultInjectedScaleExponent :: Double
  , holeSearchTermScaleFactor :: Vector2 Double
  , holeNumLabelScaleFactor :: Vector2 Double
  , holeNumLabelColor :: Draw.Color

  , typeErrorHoleWrapBackgroundColor :: Draw.Color
  , deletableHoleBackgroundColor :: Draw.Color

  , activeHoleBackgroundColor :: Draw.Color
  , inactiveHoleBackgroundColor :: Draw.Color

  , tagScaleFactor :: Vector2 Double

  , fieldTagScaleFactor :: Vector2 Double
  , fieldTint :: Draw.Color

  , inferredValueScaleFactor :: Vector2 Double
  , inferredValueTint :: Draw.Color

  , parenHighlightColor :: Draw.Color

  , lambdaWrapKeys :: [E.ModKey]
  , addWhereItemKeys :: [E.ModKey]

  , lambdaColor :: Draw.Color
  , lambdaTextSize :: Int

  , rightArrowColor :: Draw.Color
  , rightArrowTextSize :: Int

  , whereColor :: Draw.Color
  , whereScaleFactor :: Vector2 Double
  , whereLabelScaleFactor :: Vector2 Double

  , typeScaleFactor :: Vector2 Double
  , squareParensScaleFactor :: Vector2 Double

  , foreignModuleColor :: Draw.Color
  , foreignVarColor :: Draw.Color

  , cutKeys :: [E.ModKey]
  , pasteKeys :: [E.ModKey]

  , inactiveTintColor :: Draw.Color
  , activeDefBGColor :: Draw.Color

  , inferredTypeTint :: Draw.Color
  , inferredTypeErrorBGColor :: Draw.Color
  , inferredTypeBGColor :: Draw.Color

-- For definitions
  , collapsedForegroundColor :: Draw.Color
-- For parameters
  , collapsedCompactBGColor :: Draw.Color
  , collapsedExpandedBGColor :: Draw.Color
  , collapsedExpandKeys :: [E.ModKey]
  , collapsedCollapseKeys :: [E.ModKey]

  , monomorphicDefOriginForegroundColor :: Draw.Color
  , polymorphicDefOriginForegroundColor :: Draw.Color

  , builtinOriginNameColor :: Draw.Color

  , cursorBGColor :: Draw.Color

  , listBracketTextSize :: Int
  , listBracketColor :: Draw.Color
  , listCommaTextSize :: Int
  , listCommaColor :: Draw.Color

  , listAddItemKeys :: [E.ModKey]

  , selectedBranchColor :: Draw.Color

  , jumpLHStoRHSKeys :: [E.ModKey]
  , jumpRHStoLHSKeys :: [E.ModKey]

  , shrinkBaseFontKeys :: [E.ModKey]
  , enlargeBaseFontKeys :: [E.ModKey]

  , enlargeFactor :: Double
  , shrinkFactor :: Double

  , defTypeLabelTextSize :: Int
  , defTypeLabelColor :: Draw.Color

  , defTypeBoxScaleFactor :: Vector2 Double

  , acceptInferredTypeKeys :: [E.ModKey]

  , autoGeneratedNameTint :: Draw.Color
  , collisionSuffixTextColor :: Draw.Color
  , collisionSuffixBGColor :: Draw.Color
  , collisionSuffixScaleFactor :: Vector2 Double

  , paramDefSuffixScaleFactor :: Vector2 Double

  , enterSubexpressionKeys :: [E.ModKey]
  , leaveSubexpressionKeys :: [E.ModKey]

  , replaceInferredValueKeys :: [E.ModKey]
  , keepInferredValueKeys :: [E.ModKey]
  , acceptInferredValueKeys :: [E.ModKey]

  , nextInfoModeKeys :: [E.ModKey]

  , recordTypeParensColor :: Draw.Color
  , recordValParensColor :: Draw.Color
  , recordAddFieldKeys :: [E.ModKey]

  , presentationChoiceScaleFactor :: Vector2 Double
  , presentationChoiceColor :: Draw.Color

  , labeledApplyBGColor :: Draw.Color
  } deriving (Eq)

delKeys :: Config -> [E.ModKey]
delKeys config = delForwardKeys config ++ delBackwardKeys config

deriveJSON id ''Vector2
deriveJSON id ''Draw.Color
deriveJSON id ''E.ModState
deriveJSON id ''E.ModKey
deriveJSON id ''E.Key
deriveJSON id ''Config

instance FromJSON CDouble where
  parseJSON = fmap (realToFrac :: Double -> CDouble) . parseJSON

instance ToJSON CDouble where
  toJSON = toJSON . (realToFrac :: CDouble -> Double)
