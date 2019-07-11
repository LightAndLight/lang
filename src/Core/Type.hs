{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language MultiParamTypeClasses #-}
{-# language PatternSynonyms #-}
{-# language TemplateHaskell #-}
{-# language TypeFamilies #-}
module Core.Type where

import Bound.Scope.Simple (Scope, abstract1, fromScope)
import Bound.TH (makeBound)
import Data.Deriving (deriveEq1, deriveShow1)
import Data.Functor.Classes (eq1, showsPrec1)
import Data.Text (Text)

import Rep

data Type ty
  -- 'types'
  = TVar ty
  | TApp (Type ty) (Type ty) (Type ty)
  | TUInt64 (Type ty)
  | TArr (Type ty)
  | TRep (Type ty) Rep
  | TForall (Type ty) (Maybe Text) (Type ty) (Scope () Type ty)

  -- 'kinds'
  | TKRep (Type ty)
  | TKPi (Type ty) (Maybe Text) (Type ty) (Scope () Type ty)
  | TKType (Type ty) !Integer
  deriving (Functor, Foldable, Traversable)
getKind :: (ty -> Kind ty) -> Type ty -> Kind ty
getKind f ty =
  case ty of
    TVar a -> f a
    TApp a _ _ -> a
    TUInt64 a -> a
    TArr a -> a
    TRep a _ -> a
    TForall a _ _ _ -> a
    TKRep a -> a
    TKPi a _ _ _ -> a
    TKType a _ -> a
type Kind = Type
infixl 5 `TApp`
makeBound ''Type
deriveEq1 ''Type
deriveShow1 ''Type
instance Eq ty => Eq (Type ty) where; (==) = eq1
instance Show ty => Show (Type ty) where; showsPrec = showsPrec1

eqType :: Eq ty => Type ty -> Type ty -> Bool
eqType (TVar a) (TVar b) = a == b
eqType (TApp _ a b) (TApp _ a' b') = eqType a a' && eqType b b'
eqType (TUInt64 _) (TUInt64 _) = True
eqType (TArr _) (TArr _) = True
eqType (TRep _ a) (TRep _ b) = a == b
eqType (TForall _ _ a b) (TForall _ _ a' b') = eqType a a' && eqType (fromScope b) (fromScope b')
eqType (TKRep _) (TKRep _) = True
eqType (TKPi _ _ a b) (TKPi _ _ a' b') = eqType a a' && eqType (fromScope b) (fromScope b')
eqType (TKType _ a) (TKType _ b) = a == b
eqType _ _ = False

tforall_ :: Kind Text -> (Text, Type Text) -> Type Text -> Type Text
tforall_ x (a, s) = TForall x (Just a) s . abstract1 a