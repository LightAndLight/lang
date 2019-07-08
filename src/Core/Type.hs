{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language MultiParamTypeClasses #-}
{-# language PatternSynonyms #-}
{-# language TemplateHaskell #-}
module Core.Type where

import Biscope (Bisubst(..), BiscopeR(..), abs1BiscopeR, bisubstBiscopeR)
import Bound.Scope.Simple (Scope, abstract1)
import Bound.TH (makeBound)
import Control.Monad (ap)
import Data.Bifunctor.TH (deriveBifunctor, deriveBifoldable, deriveBitraversable)
import Data.Deriving (deriveEq2, deriveShow2, deriveEq1, deriveShow1)
import Data.Functor.Classes
  (Eq2(..), Eq1(..), Show2(..), Show1(..), eq1, showsPrec1)
import Data.Text (Text)

data Kind ki
  = KVar ki
  | KForall (Maybe Text) (Scope () Kind ki)
  | KType (Kind ki)
  | KBoxedRep
  | KIntRep
  | KArr (Kind ki) (Kind ki)
  deriving (Functor, Foldable, Traversable)
makeBound ''Kind
deriveEq1 ''Kind
deriveShow1 ''Kind
instance Eq ki => Eq (Kind ki) where; (==) = eq1
instance Show ki => Show (Kind ki) where; showsPrec = showsPrec1

kforall_ :: Text -> Kind Text -> Kind Text
kforall_ a b = KForall (Just a) $ abstract1 a b

data Type ki ty
  = TVar ty
  | TForall (Maybe Text) (Kind ki) (BiscopeR () Kind Type ki ty)
  | TApp (Type ki ty) (Type ki ty)
  | TAppKind (Type ki ty) (Kind ki)
  | TArr
  | TUInt64
  deriving (Functor, Foldable, Traversable)

instance Bisubst Type Kind where
  bireturn = TVar
  bisubst f g ty =
    case ty of
      TVar a -> g a
      TForall n k a -> TForall n (k >>= f) (bisubstBiscopeR f g a)
      TAppKind a b -> TAppKind (bisubst f g a) (b >>= f)
      TApp a b -> TApp (bisubst f g a) (bisubst f g b)
      TArr -> TArr
      TUInt64 -> TUInt64

instance Applicative (Type ki) where; pure = return; (<*>) = ap
instance Monad (Type ki) where return = bireturn; (>>=) a f = bisubst pure f a

substKi :: (ki -> Kind ki') -> Type ki ty -> Type ki' ty
substKi f = bisubst f pure

tforall_ :: (Text, Kind ki) -> Type ki Text -> Type ki Text
tforall_ (a, k) = TForall (Just a) k . abs1BiscopeR a

deriveBifunctor ''Type
deriveBifoldable ''Type
deriveBitraversable ''Type
deriveEq2 ''Type
deriveShow2 ''Type
instance Eq ki => Eq1 (Type ki) where; liftEq = liftEq2 (==)
instance (Eq ki, Eq ty) => Eq (Type ki ty) where; (==) = eq1
instance Show ki => Show1 (Type ki) where; liftShowsPrec = liftShowsPrec2 showsPrec showList
instance (Show ki, Show ty) => Show (Type ki ty) where; showsPrec = showsPrec1

pattern TArrow :: Type ki ty -> Type ki ty -> Type ki ty
pattern TArrow a b = TApp (TApp TArr a) b
