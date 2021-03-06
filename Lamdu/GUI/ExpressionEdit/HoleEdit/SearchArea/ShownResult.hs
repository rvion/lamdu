{-# LANGUAGE TemplateHaskell #-}
module Lamdu.GUI.ExpressionEdit.HoleEdit.SearchArea.ShownResult
    ( PickedResult(..), pickedEventResult, pickedIdTranslations
    , ShownResult(..)
    ) where

import qualified Control.Lens as Lens
import qualified Data.Store.Transaction as Transaction
import qualified Graphics.UI.Bottle.Widget as Widget
import           Lamdu.GUI.ExpressionGui.Monad (ExprGuiM)
import           Lamdu.Sugar.Names.Types (Name)
import qualified Lamdu.Sugar.Types as Sugar

type T = Transaction.Transaction

data PickedResult = PickedResult
    { _pickedEventResult :: Widget.EventResult
    , _pickedIdTranslations :: Widget.Id -> Widget.Id
    }
Lens.makeLenses ''PickedResult

data ShownResult m = ShownResult
    { srMkEventMap :: ExprGuiM m (Widget.EventHandlers (T m))
    , srHoleResult :: Sugar.HoleResult (Name m) m
    , srPick :: T m PickedResult
    }
