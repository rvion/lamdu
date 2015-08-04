{-# LANGUAGE NoImplicitPrelude, DeriveFunctor, DeriveFoldable, DeriveTraversable, GeneralizedNewtypeDeriving, OverloadedStrings, TemplateHaskell #-}

module Lamdu.Eval
    ( EvalT(..)
    , EvalState, initialState
    , ask
    , EvalActions(..)
    , Env(..), eEvalActions
    , Event(..), EventLambdaApplied(..), EventResultComputed(..)
    , ScopedVal(..)
    , evalScopedVal
    ) where

import           Prelude.Compat

import           Control.Lens (at, use)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad.Trans.Class (MonadTrans(..))
import           Control.Monad.Trans.Either (EitherT(..), left, hoistEither)
import           Control.Monad.Trans.State.Strict (StateT(..))
import           Control.MonadA (MonadA)
import           Data.Map (Map)
import qualified Data.Map.Strict as Map
import qualified Lamdu.Data.Definition as Def
import           Lamdu.Eval.Val (Val(..), EvalResult, EvalError(..), Closure(..), Scope(..), emptyScope, ScopeId(..), scopeIdInt)
import qualified Lamdu.Expr.Val as V

data ScopedVal pl = ScopedVal
    { _srcScope :: !(Scope pl)
    , _srcExpr :: !(V.Val pl)
    } deriving (Show, Functor, Foldable, Traversable)

data EventLambdaApplied pl = EventLambdaApplied
    { elaLam :: pl
    , elaParentId :: !ScopeId
    , elaId :: !ScopeId
    , elaArgument :: !(EvalResult pl)
    } deriving (Show, Functor, Foldable, Traversable)

data EventResultComputed pl = EventResultComputed
    { ercSource :: pl
    , ercScope :: !ScopeId
    , ercResult :: !(EvalResult pl)
    } deriving (Show, Functor, Foldable, Traversable)

data Event pl
    = ELambdaApplied (EventLambdaApplied pl)
    | EResultComputed (EventResultComputed pl)
    deriving (Show, Functor, Foldable, Traversable)

data EvalActions m pl = EvalActions
    { _aReportEvent :: Event pl -> m ()
    , _aRunBuiltin :: Def.FFIName -> Val pl -> EvalResult pl
    , _aLoadGlobal :: V.GlobalId -> m (Maybe (Def.Body (V.Val pl)))
    }

newtype Env m pl = Env
    { _eEvalActions :: EvalActions m pl
    }

data EvalState m pl = EvalState
    { _esScopeCounter :: !ScopeId
    , _esLoadedGlobals :: !(Map V.GlobalId (Val pl))
    , _esReader :: !(Env m pl) -- This is ReaderT
    }

newtype EvalT pl m a = EvalT
    { runEvalT :: StateT (EvalState m pl) m a
    } deriving (Functor, Applicative, Monad)

liftState :: Monad m => StateT (EvalState m pl) m a -> EvalT pl m a
liftState = EvalT

instance MonadTrans (EvalT pl) where
    lift = liftState . lift

Lens.makeLenses ''Scope
Lens.makeLenses ''EvalActions
Lens.makeLenses ''Env
Lens.makeLenses ''EvalState

ask :: Monad m => EvalT pl m (Env m pl)
ask = use esReader & liftState

report :: MonadA m => Event pl -> EvalT pl m ()
report event =
    do
        rep <- ask <&> (^. eEvalActions . aReportEvent)
        rep event & lift

bindVar :: MonadA m => pl -> V.Var -> Val pl -> Scope pl -> EvalT pl m (Scope pl)
bindVar lamPl var val (Scope parentMap parentId) =
    do
        newScopeId <- liftState $ use esScopeCounter
        liftState $ esScopeCounter . scopeIdInt += 1
        EventLambdaApplied
            { elaLam = lamPl
            , elaParentId = parentId
            , elaId = newScopeId
            , elaArgument = Right val
            } & ELambdaApplied & report
        Scope
            { _scopeId = newScopeId
            , _scopeMap = parentMap & at var .~ Just val
            } & return

evalApply ::
    MonadA m => V.Apply (Val pl) -> EitherT EvalError (EvalT pl m) (Val pl)
evalApply (V.Apply func arg) =
    case func of
    HFunc (Closure outerScope (V.Lam var body) lamPl) ->
        bindVar lamPl var arg outerScope & lift
        >>= EitherT . evalScopedVal . (`ScopedVal` body)
    HBuiltin ffiname ->
        do
            runBuiltin <- lift ask <&> (^. eEvalActions . aRunBuiltin)
            runBuiltin ffiname arg & hoistEither
    HCase (V.Case caseTag handlerFunc rest) ->
        case arg of
        HInject (V.Inject sumTag injected) ->
            ( if caseTag == sumTag
                then V.Apply <$> handlerFunc <*> injected
                else V.Apply <$> rest <*> pure arg
            ) & hoistEither >>= evalApply
        _ -> left EvalError
    _ -> left EvalError

evalScopedVal :: MonadA m => ScopedVal pl -> EvalT pl m (EvalResult pl)
evalScopedVal (ScopedVal scope expr) =
    reportResultComputed =<<
    case expr ^. V.body of
    V.BAbs lam ->
        Closure scope lam (expr ^. V.payload) & HFunc & Right & return
    V.BApp apply ->
        traverse inner apply <&> sequenceA
        & EitherT >>= evalApply & runEitherT
    V.BGetField getField ->
        getField & traverse inner <&> sequenceA
        & EitherT >>= evalGetField & runEitherT
    V.BInject    inject    -> traverse inner inject    <&> Right . HInject
    V.BRecExtend recExtend -> traverse inner recExtend <&> Right . HRecExtend
    V.BCase      case_     -> traverse inner case_     <&> Right . HCase
    V.BFromNom (V.Nom _ v) -> inner v
    V.BToNom   (V.Nom _ v) -> inner v
    V.BLeaf (V.LGlobal global) -> loadGlobal global
    V.BLeaf (V.LVar var) ->
        case scope ^. scopeMap . at var of
        Nothing -> Left EvalError & return
        Just val -> Right val & return
    V.BLeaf V.LRecEmpty -> Right HRecEmpty & return
    V.BLeaf V.LAbsurd   -> Right HAbsurd & return
    V.BLeaf (V.LLiteralInteger i) -> HInteger i & Right & return
    V.BLeaf V.LHole -> Left EvalError & return
    where
        inner = evalScopedVal . ScopedVal scope
        reportResultComputed result =
            do
                EventResultComputed (expr ^. V.payload) (scope ^. scopeId) result
                    & EResultComputed & report
                return result

evalGetField ::
    Monad m => V.GetField (Val pl) -> EitherT EvalError (EvalT pl m) (Val pl)
evalGetField (V.GetField (HRecExtend (V.RecExtend tag val rest)) searchTag)
    | searchTag == tag = return val & EitherT
    | otherwise =
        V.GetField rest searchTag & sequenceA & hoistEither >>= evalGetField
evalGetField _ = left EvalError

loadGlobal :: MonadA m => V.GlobalId -> EvalT pl m (EvalResult pl)
loadGlobal g =
    do
        loaded <- liftState $ use (esLoadedGlobals . at g)
        case loaded of
            Just cached -> Right cached & return
            Nothing -> do
                loader <- ask <&> (^. eEvalActions . aLoadGlobal)
                mLoadedGlobal <- lift $ loader g
                result <-
                    case mLoadedGlobal of
                    Nothing -> Left EvalError & return
                    Just (Def.BodyBuiltin (Def.Builtin name _t)) ->
                        HBuiltin name & Right & return
                    Just (Def.BodyExpr (Def.Expr expr _t)) ->
                        evalScopedVal $ ScopedVal emptyScope expr
                case result of
                    Left _ -> return ()
                    Right r ->
                        liftState $ esLoadedGlobals . at g .= Just r
                return result

initialState :: Env m pl -> EvalState m pl
initialState env =
    EvalState
    { _esScopeCounter = ScopeId 1
    , _esLoadedGlobals = Map.empty
    , _esReader = env
    }
