{-# LANGUAGE NoImplicitPrelude, OverloadedStrings, DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module Lamdu.Builtins
    ( eval
    ) where

import           Prelude.Compat

import           Control.Lens.Operators
import           Control.Monad (join, void)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Map.Utils (matchKeys)
import qualified Lamdu.Builtins.Anchors as Builtins
import qualified Lamdu.Data.Definition as Def
import           Lamdu.Eval.Val (Val(..), EvalResult, EvalError(..))
import           Lamdu.Expr.Type (Tag)
import qualified Lamdu.Expr.Type as T
import qualified Lamdu.Expr.Val as V

flatRecord :: Val pl -> Map Tag (EvalResult pl)
flatRecord HRecEmpty = Map.empty
flatRecord (HRecExtend (V.RecExtend t v rest)) =
    either (const Map.empty) flatRecord rest & Map.insert t v
flatRecord _ = error "Param record is not a record"

extractRecordParams ::
    (Traversable t, Show (t Tag)) =>
    t Tag -> Val pl -> Either EvalError (t (Val pl))
extractRecordParams expectedTags val =
    case matchKeys expectedTags paramsMap of
    Nothing -> Left EvalError
    Just x -> sequenceA x
    where
        paramsMap = flatRecord val

data V2 a = V2 a a   deriving (Show, Functor, Foldable, Traversable)
data V3 a = V3 a a a deriving (Show, Functor, Foldable, Traversable)

extractInfixParams :: Val pl -> Either EvalError (V2 (Val pl))
extractInfixParams =
        extractRecordParams (V2 Builtins.infixlTag Builtins.infixrTag)

class GuestType t where
    toGuest :: t -> Val pl
    fromGuest :: Val pl -> Either EvalError t

instance GuestType Integer where
    toGuest = HInteger
    fromGuest (HInteger x) = Right x
    fromGuest x = error $ "expected int, got " ++ show (void x)

instance GuestType Bool where
    toGuest b =
        record [] & Right & V.Inject (tag b) & HInject
        where
            tag True = Builtins.trueTag
            tag False = Builtins.falseTag
    fromGuest v =
        case v of
        HInject (V.Inject boolTag _)
            | boolTag == Builtins.trueTag -> Right True
            | boolTag == Builtins.falseTag -> Right False
        _ -> Left EvalError

record :: [(T.Tag, Val pl)] -> Val pl
record [] = HRecEmpty
record ((tag, val) : xs) =
    record xs & Right & V.RecExtend tag (Right val) & HRecExtend

instance GuestType t => GuestType [t] where
    toGuest [] = record [] & Right & V.Inject "[]" & HInject
    toGuest (x:xs) =
        record
        [ ("head", toGuest x)
        , ("tail", toGuest xs)
        ] & Right & V.Inject "[]" & HInject
    fromGuest (HInject (V.Inject t v))
        | t == "[]" = Right []
        | t == ":" =
            case v of
            Left _ -> Left EvalError
            Right val ->
                case (Map.lookup "head" fields, Map.lookup "tail" fields) of
                (Just (Right hd), Just (Right tl)) ->
                    (:) <$> fromGuest hd <*> fromGuest tl
                _ -> Left EvalError
                where
                    fields = flatRecord val
    fromGuest x = error $ "Expected list: got " ++ show (void x)

builtin1 :: (GuestType a, GuestType b) => (a -> b) -> Val pl -> EvalResult pl
builtin1 f val = fromGuest val <&> f <&> toGuest

builtin2Infix ::
    ( GuestType a
    , GuestType b
    , GuestType c ) =>
    (a -> b -> c) -> Val pl -> EvalResult pl
builtin2Infix f thunkId =
    do
        V2 x y <- extractInfixParams thunkId
        f <$> fromGuest x <*> fromGuest y <&> toGuest

eq :: Val t -> Val t -> Either EvalError Bool
eq HFunc {} _    = Left EvalError
eq HAbsurd {} _  = Left EvalError
eq HCase {} _    = Left EvalError
eq HBuiltin {} _ = Left EvalError
eq (HInteger x) (HInteger y) = x == y & Right
eq (HRecExtend x) (HRecExtend y)
    | Map.keysSet fx /= Map.keysSet fy = Left EvalError
    | otherwise =
        Map.intersectionWith eq <$> sequenceA fx <*> sequenceA fy
        <&> Map.elems <&> sequence & join <&> and
    where
        fx = HRecExtend x & flatRecord
        fy = HRecExtend y & flatRecord
eq HRecEmpty HRecEmpty = Right True
eq (HInject (V.Inject xf xv)) (HInject (V.Inject yf yv))
    | xf == yf = eq <$> xv <*> yv & join
    | otherwise = Right False
eq _ _ = Right False -- assume type checking ruled out errorenous equalities already

builtinEqH :: GuestType t => (Bool -> t) -> Val pl -> EvalResult pl
builtinEqH f val =
    do
        V2 x y <- extractInfixParams val
        eq x y <&> f <&> toGuest

builtinEq :: Val pl -> EvalResult pl
builtinEq = builtinEqH id

builtinNotEq :: Val pl -> EvalResult pl
builtinNotEq = builtinEqH not

intArg :: (Integer -> a) -> Integer -> a
intArg = id

eval :: Def.FFIName -> Val pl -> EvalResult pl
eval name =
    case name of
    Def.FFIName ["Prelude"] "=="     -> builtinEq
    Def.FFIName ["Prelude"] "/="     -> builtinNotEq
    Def.FFIName ["Prelude"] "<"      -> builtin2Infix $ intArg (<)
    Def.FFIName ["Prelude"] "<="     -> builtin2Infix $ intArg (<=)
    Def.FFIName ["Prelude"] ">"      -> builtin2Infix $ intArg (>)
    Def.FFIName ["Prelude"] ">="     -> builtin2Infix $ intArg (>=)
    Def.FFIName ["Prelude"] "*"      -> builtin2Infix $ intArg (*)
    Def.FFIName ["Prelude"] "+"      -> builtin2Infix $ intArg (+)
    Def.FFIName ["Prelude"] "-"      -> builtin2Infix $ intArg (-)
    Def.FFIName ["Prelude"] "div"    -> builtin2Infix $ intArg div
    Def.FFIName ["Prelude"] "mod"    -> builtin2Infix $ intArg mod
    Def.FFIName ["Prelude"] "negate" -> builtin1      $ intArg negate
    Def.FFIName ["Prelude"] "sqrt"   -> builtin1      $ intArg ((floor :: Double -> Integer) . sqrt . fromIntegral)
    _ -> error $ show name ++ " not yet supported"
