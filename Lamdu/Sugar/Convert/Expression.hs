module Lamdu.Sugar.Convert.Expression
  ( make
  , mkReplaceWithNewHole
  , makeStoredNameProperty
  ) where

import Control.Applicative (Applicative(..), (<$>))
import Control.Lens.Operators
import Control.MonadA (MonadA)
import Data.Store.Guid (Guid)
import Data.Store.Transaction (Transaction)
import Lamdu.Sugar.Convert.Monad (ConvertM)
import Lamdu.Sugar.Internal
import Lamdu.Sugar.Types
import qualified Data.Store.Property as Property
import qualified Data.Store.Transaction as Transaction
import qualified Lamdu.Data.Anchors as Anchors
import qualified Lamdu.Data.Ops as DataOps
import qualified Lamdu.Expr.IRef as ExprIRef
import qualified Lamdu.Expr.UniqueId as UniqueId
import qualified Lamdu.Infer as Infer
import qualified Lamdu.Sugar.Convert.Monad as ConvertM

type T = Transaction

mkCutter ::
  MonadA m => Anchors.CodeProps m -> ExprIRef.ValIM m -> T m Guid -> T m Guid
mkCutter cp expr replaceWithHole = do
  _ <- DataOps.newClipboard cp expr
  replaceWithHole

mkReplaceWithNewHole :: MonadA m => ExprIRef.ValIProperty m -> T m Guid
mkReplaceWithNewHole stored =
  ExprIRef.valIGuid <$> DataOps.replaceWithHole stored

mkActions :: MonadA m => ConvertM.Context m -> ExprIRef.ValIProperty m -> Actions m
mkActions sugarContext stored =
  Actions
  { _wrap = WrapAction $ ExprIRef.valIGuid <$> DataOps.wrap stored
  , _setToHole = SetToHole $ ExprIRef.valIGuid <$> DataOps.setToHole stored
  , _setToInnerExpr = NoInnerExpr
  , _cut =
    mkCutter (sugarContext ^. ConvertM.scCodeAnchors)
    (Property.value stored) $ mkReplaceWithNewHole stored
  }

make ::
  MonadA m => InputPayload m a -> BodyU m a -> ConvertM m (ExpressionU m a)
make exprPl body = do
  sugarContext <- ConvertM.readContext
  return $ Expression body Payload
    { _plGuid = exprPl ^. ipGuid
    , _plInferredType = exprPl ^. ipInferred . Infer.plType
    , _plActions = mkActions sugarContext <$> exprPl ^. ipStored
    , _plData = exprPl ^. ipData
    }

makeStoredNameProperty ::
  (UniqueId.ToGuid a, MonadA m) => a -> T m (NameProperty MStoredName m)
makeStoredNameProperty uid = do
  name <- Transaction.getP nameRef
  pure
    NameProperty
    { _npName = if null name then Nothing else Just name
    , _npGuid = UniqueId.toGuid uid
    , _npSetName = Transaction.setP nameRef
    }
  where
    nameRef = Anchors.assocNameRef uid
