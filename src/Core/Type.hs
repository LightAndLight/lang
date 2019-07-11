{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language MultiParamTypeClasses #-}
{-# language PatternSynonyms #-}
{-# language TemplateHaskell #-}
{-# language TypeFamilies #-}
module Core.Type where

import Bound.Scope.Simple (Scope, abstract1)
import Bound.TH (makeBound)
import Data.Deriving (deriveEq1, deriveShow1)
import Data.Functor.Classes (eq1, showsPrec1)
import Data.Text (Text)

data Rep = RPtr | RI64 | RList [Rep]
  deriving (Eq, Show)

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
infixl 5 `TApp`
makeBound ''Type
deriveEq1 ''Type
deriveShow1 ''Type
instance Eq ty => Eq (Type ty) where; (==) = eq1
instance Show ty => Show (Type ty) where; showsPrec = showsPrec1

type Kind = Type

pattern TArrow :: Type ty -> Type ty -> Type ty -> Type ty -> Type ty
pattern TArrow r1 r2 s t = TApp (TApp (TApp (TApp TArr r1) r2) s) t

tforall_ :: (Text, Type Text) -> Type Text -> Type Text
tforall_ (a, s) = TForall (Just a) s . abstract1 a