{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language OverloadedStrings #-}
{-# language RankNTypes #-}
{-# language TemplateHaskell #-}
{-# language TypeFamilies #-}
module Core where

import Biscope (Bisubst(..), BiscopeL, BiscopeR, bisubstBiscopeR, bisubstBiscopeL)
import Bound.Scope.Simple (toScope)
import Bound.Var (Var(..))
import Control.Monad (ap)
import Data.Bifunctor.TH (deriveBifunctor, deriveBifoldable, deriveBitraversable)
import Data.Deriving (deriveEq2, deriveShow2, deriveEq1, deriveShow1)
import Data.Functor.Classes (eq1, showsPrec1)
import Data.Word (Word64)
import Data.Text (Text)

import Core.Type (Type(..), Kind)
import Operators (Op)
import Rep (Rep(..))

data ArrowType ty
  = ArrowType
  { atInKind :: Kind ty
  , atOutKind :: Kind ty
  , atInType :: Type ty
  , atOutType :: Type ty
  } deriving (Eq, Show, Functor, Foldable, Traversable)
deriveEq1 ''ArrowType
deriveShow1 ''ArrowType
bindArrowType :: (a -> Type b) -> ArrowType a -> ArrowType b
bindArrowType f (ArrowType a b c d) = ArrowType (a >>= f) (b >>= f) (c >>= f) (d >>= f)

data Core ty tm
  = Var tm
  | UInt64 (Type ty) !Word64
  | Bin (Type ty) Op (Core ty tm) (Core ty tm)
  | Lam (ArrowType ty) (Maybe Text) (Type ty) (BiscopeR () Type Core ty tm)
  | App (Type ty) (Core ty tm) (Core ty tm)
  | AppType (Type ty) (Core ty tm) (Type ty)
  | AbsType (Type ty) (Maybe Text) (Kind ty) (BiscopeL () Type Core ty tm)
  deriving (Functor, Foldable, Traversable)
deriveBifunctor ''Core
deriveBifoldable ''Core
deriveBitraversable ''Core

instance Bisubst Core where
  type Inner Core = Type
  bireturn = Var
  bisubst f g tm =
    case tm of
      Var a -> g a
      UInt64 x a -> UInt64 (x >>= f) a
      Bin x a b c -> Bin (x >>= f) a (bisubst f g b) (bisubst f g c)
      Lam x a b c ->
        Lam (bindArrowType f x) a (b >>= f) (bisubstBiscopeR f g c)
      App x a b -> App (x >>= f) (bisubst f g a) (bisubst f g b)
      AppType x a b -> AppType (x >>= f) (bisubst f g a) (b >>= f)
      AbsType x a b c -> AbsType (x >>= f) a (b >>= f) (bisubstBiscopeL f g c)

instance Applicative (Core ty) where; pure = return; (<*>) = ap
instance Monad (Core ty) where; return = bireturn; (>>=) a f = bisubst pure f a

deriveEq2 ''Core
deriveShow2 ''Core
deriveEq1 ''Core
deriveShow1 ''Core
instance (Eq ty, Eq tm) => Eq (Core ty tm) where; (==) = eq1
instance (Show ty, Show tm) => Show (Core ty tm) where; showsPrec = showsPrec1

data Def ty tm = Def tm (Core ty tm) (Type ty)
  deriving Show

getType :: (tm -> Type ty) -> Core ty tm -> Type ty
getType f ty =
  case ty of
    Var a -> f a
    UInt64 a _ -> a
    Bin a _ _ _ -> a
    Lam (ArrowType a b c d) _ _ _ ->
      let
        k = TKType 1 (TRep RPtr)

        k1 =
          TKPi k (Just "r2") TKRep . toScope $
          TKPi k Nothing (TKType 0 $ F <$> a) . toScope $
          TKPi k Nothing (TKType 0 $ TVar $ F $ B ()) . toScope $
          k4
        t1 = TApp k1 TArr a

        k2 =
          TKPi k Nothing (TKType 0 a) . toScope $
          TKPi k Nothing (TKType 0 $ F <$> b) . toScope $
          k4
        t2 = TApp k2 t1 b

        k3 =
          TKPi k Nothing (TKType 0 b) . toScope $
          k4
        t3 = TApp k3 t2 c

        k4 = TKType 0 (TRep RPtr)
        t4 = TApp k4 t3 d
      in
        t4
    App a _ _ -> a
    AppType a _ _ -> a
    AbsType a _ _ _ -> a