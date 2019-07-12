{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language MultiParamTypeClasses #-}
{-# language PatternSynonyms #-}
{-# language TemplateHaskell #-}
{-# language TypeFamilies #-}
module Syntax.Type where

import Bound.Scope.Simple (Scope, abstract1, fromScope)
import Bound.TH (makeBound)
import Data.Deriving (deriveEq1, deriveShow1)
import Data.Functor.Classes (eq1, showsPrec1)
import Data.Text (Text)

import Rep

data Type ty
  -- 'types'
  = TVar ty
  | TApp (Type ty) (Type ty)
  | TUInt64
  | TArr
  | TRep Rep
  | TForall (Maybe Text) (Type ty) (Scope () Type ty)

  -- 'kinds'
  | TKRep
  | TKPi (Maybe Text) (Type ty) (Scope () Type ty)
  | TKType !Integer
  deriving (Functor, Foldable, Traversable)
type Kind = Type
infixl 5 `TApp`
makeBound ''Type
deriveEq1 ''Type
deriveShow1 ''Type
instance Eq ty => Eq (Type ty) where; (==) = eq1
instance Show ty => Show (Type ty) where; showsPrec = showsPrec1

tforall_ :: (Text, Type Text) -> Type Text -> Type Text
tforall_ (a, s) = TForall (Just a) s . abstract1 a

eqType :: Eq ty => Type ty -> Type ty -> Bool
eqType (TVar a) (TVar b) = a == b
eqType (TApp a b) (TApp a' b') = eqType a a' && eqType b b'
eqType TUInt64 TUInt64 = True
eqType TArr TArr = True
eqType (TRep a) (TRep b) = a == b
eqType (TForall _ a b) (TForall _ a' b') = eqType a a' && eqType (fromScope b) (fromScope b')
eqType TKRep TKRep = True
eqType (TKPi _ a b) (TKPi _ a' b') = eqType a a' && eqType (fromScope b) (fromScope b')
eqType (TKType a) (TKType b) = a == b
eqType _ _ = False