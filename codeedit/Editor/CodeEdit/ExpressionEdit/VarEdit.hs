{-# LANGUAGE OverloadedStrings, TypeFamilies #-}
module Editor.CodeEdit.ExpressionEdit.VarEdit(make, makeView) where

import Control.MonadA (MonadA)
import Editor.Anchors (ViewM)
import Editor.CodeEdit.ExpressionEdit.ExpressionGui (ExpressionGui)
import Editor.CodeEdit.ExpressionEdit.ExpressionGui.Monad (ExprGuiM)
import qualified Control.Lens as Lens
import qualified Editor.BottleWidgets as BWidgets
import qualified Editor.CodeEdit.ExpressionEdit.ExpressionGui as ExpressionGui
import qualified Editor.CodeEdit.ExpressionEdit.ExpressionGui.Monad as ExprGuiM
import qualified Editor.Config as Config
import qualified Editor.Data as Data
import qualified Editor.Data.IRef as DataIRef
import qualified Editor.Data.Ops as DataOps
import qualified Editor.WidgetEnvT as WE
import qualified Editor.WidgetIds as WidgetIds
import qualified Graphics.DrawingCombinators as Draw
import qualified Graphics.UI.Bottle.Widget as Widget

colorOf :: Data.VariableRef DataIRef.DefI -> Draw.Color
colorOf (Data.DefinitionRef _) = Config.definitionColor
colorOf (Data.ParameterRef _) = Config.parameterColor

-- Color should be determined on the outside!
makeView
  :: MonadA m
  => Data.VariableRef DataIRef.DefI
  -> Widget.Id
  -> ExprGuiM m (ExpressionGui m)
makeView var myId = ExprGuiM.withNameFromVarRef var $ \(nameSrc, name) ->
  fmap
  (ExpressionGui.fromValueWidget .
   ExpressionGui.nameSrcTint nameSrc) .
  ExprGuiM.widgetEnv $
  BWidgets.makeFocusableTextView name myId

make
  :: m ~ ViewM
  => Data.VariableRef DataIRef.DefI
  -> Widget.Id
  -> ExprGuiM m (ExpressionGui m)
make getVar myId = do
  case getVar of
    Data.ParameterRef guid -> ExprGuiM.markVariablesAsUsed [guid]
    _ -> return ()
  getVarView <-
    ExprGuiM.atEnv (WE.setTextColor (colorOf getVar)) $
    makeView getVar myId
  let
    jumpToDefinitionEventMap =
      Widget.keysEventMapMovesCursor Config.jumpToDefinitionKeys "Jump to definition"
      jumpToDefinition
    jumpToDefinition =
      case getVar of
        Data.DefinitionRef defI -> do
          DataOps.newPane defI
          DataOps.savePreJumpPosition myId
          return $ WidgetIds.fromIRef defI
        Data.ParameterRef paramGuid -> do
          DataOps.savePreJumpPosition myId
          return $ WidgetIds.fromGuid paramGuid
  return $
    Lens.over ExpressionGui.egWidget
    (Widget.weakerEvents jumpToDefinitionEventMap)
    getVarView
