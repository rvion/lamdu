{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveGeneric, TemplateHaskell #-}

-- | View and Branch have a cyclic dependency. This module
-- | contains the parts of both that both may depend on, to avoid the
-- | cycle.
module Data.Store.Rev.ViewBranchInternal
    ( ViewData(..), vdBranch
    , View(..)
    , BranchData(..), brVersion, brViews
    , Branch(..)
    , moveView, applyChangesToView, makeViewKey
    )
where

import qualified Control.Lens as Lens
import           Control.MonadA (MonadA)
import           Data.Binary (Binary(..))
import           Data.Foldable (traverse_)
import           Data.Store.Guid (Guid)
import qualified Data.Store.Guid as Guid
import           Data.Store.IRef (IRef)
import qualified Data.Store.IRef as IRef
import           Data.Store.Rev.Change (Change)
import qualified Data.Store.Rev.Change as Change
import           Data.Store.Rev.Version (Version)
import qualified Data.Store.Rev.Version as Version
import           Data.Store.Transaction (Transaction)
import qualified Data.Store.Transaction as Transaction
import           GHC.Generics (Generic)

-- This key is XOR'd with object keys to yield the IRef to each
-- object's current version ref:
newtype View m = View (IRef m (ViewData m))
    deriving (Eq, Ord, Binary, Show, Read)

data BranchData m = BranchData
    { _brVersion :: Version m
    , _brViews :: [View m]
    } deriving (Eq, Ord, Read, Show, Generic)
instance Binary (BranchData m)

newtype Branch m = Branch { unBranch :: IRef m (BranchData m) }
    deriving (Eq, Ord, Read, Show, Binary)

newtype ViewData m = ViewData { _vdBranch :: Branch m }
    deriving (Eq, Ord, Show, Read, Binary)

Lens.makeLenses ''BranchData
Lens.makeLenses ''ViewData

-- | moveView must be given the correct source of the movement
-- | or it will result in undefined results!
moveView :: MonadA m => View m -> Version m -> Version m -> Transaction m ()
moveView vm =
    Version.walk applyBackward applyForward
    where
        applyForward = apply Change.newValue
        applyBackward = apply Change.oldValue
        apply changeDir version = applyChangesToView vm changeDir . Version.changes $ version

makeViewKey :: View m -> Change.Key -> Guid
makeViewKey (View iref) = Guid.combine . IRef.guid $ iref

applyChangesToView ::
    MonadA m => View m -> (Change -> Maybe Change.Value) ->
    [Change] -> Transaction m ()
applyChangesToView vm changeDir = traverse_ applyChange
    where
        applyChange change =
            setValue
            (makeViewKey vm $ Change.objectKey change)
            (changeDir change)
        setValue key Nothing = Transaction.delete key
        setValue key (Just value) = Transaction.insertBS key value
