{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language MultiParamTypeClasses #-}
{-# language OverloadedStrings #-}
{-# language PatternSynonyms #-}
{-# language TemplateHaskell #-}
{-# language TypeFamilies #-}
module Core.Type where

import Bound.Scope.Simple (Scope, abstract1, fromScope, toScope)
import Bound.TH (makeBound)
import Bound.Var (Var(..))
import Data.Deriving (deriveEq1, deriveShow1)
import Data.Functor.Classes (eq1, showsPrec1)
import Data.Text (Text)

import Rep

data Type ty
  -- 'types'
  = TVar ty
  | TApp (Type ty) (Type ty) (Type ty)
  | TUInt64
  | TArr
  | TRep Rep
  | TForall (Type ty) (Maybe Text) (Type ty) (Scope () Type ty)

  -- 'kinds'
  | TKRep
  | TKPi (Type ty) (Maybe Text) (Type ty) (Scope () Type ty)
  | TKType !Integer (Type ty)
  deriving (Functor, Foldable, Traversable)
getKind :: (ty -> Kind ty) -> Type ty -> Kind ty
getKind f ty =
  case ty of
    TVar a -> f a
    TApp a _ _ -> a
    TUInt64 -> TKType 0 (TRep RI64)
    TArr ->
      let t = TKType 1 (TRep RPtr) in
      TKPi t (Just "r1") TKRep . toScope $
      TKPi t (Just "r2") TKRep . toScope $
      TKPi t Nothing (TKType 0 . TVar $ F$B()) . toScope $
      TKPi t Nothing (TKType 0 . TVar $ F$B()) . toScope $
      TKType 0 (TRep RPtr)
    TRep{} -> TKRep
    TForall a _ _ _ -> a
    TKRep -> TKType 0 (TRep RPtr)
    TKPi a _ _ _ -> a
    TKType n _ -> TKType (n+1) (TRep RPtr)
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
eqType TUInt64 TUInt64 = True
eqType TArr{} TArr{} = True
eqType (TRep a) (TRep b) = a == b
eqType (TForall _ _ a b) (TForall _ _ a' b') = eqType a a' && eqType (fromScope b) (fromScope b')
eqType TKRep TKRep = True
eqType (TKPi _ _ a b) (TKPi _ _ a' b') = eqType a a' && eqType (fromScope b) (fromScope b')
eqType (TKType a b) (TKType a' b') = a == a' && eqType b b'
eqType _ _ = False

tforall_ :: Kind Text -> (Text, Type Text) -> Type Text -> Type Text
tforall_ x (a, s) = TForall x (Just a) s . abstract1 a