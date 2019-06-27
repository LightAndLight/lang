{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language StandaloneDeriving #-}
{-# language TemplateHaskell #-}
module Syntax where

import Bound.Scope (Scope, fromScope)
import Bound.TH (makeBound)
import Bound.Var (unvar)
import Data.Deriving (deriveShow1)
import Data.Functor.Classes (showsPrec1)
import Data.List (union)
import Data.Word (Word64)

import qualified Data.Map as Map

data Expr a
  = Var a
  | UInt64 !Word64
  | Add (Expr a) (Expr a)
  | Mult (Expr a) (Expr a)
  | Lam (Scope () Expr a)
  | App (Expr a) (Expr a)
  deriving (Functor, Foldable, Traversable)
makeBound ''Expr
deriveShow1 ''Expr
instance Show a => Show (Expr a) where; showsPrec = showsPrec1

data C_Expr a
  = C_Var a
  | C_Bound
  | C_Env !Word64
  | C_UInt64 !Word64
  | C_Add (C_Expr a) (C_Expr a)
  | C_Mult (C_Expr a) (C_Expr a)
  | C_Lam [C_Expr a] (C_Expr a)
  | C_App (C_Expr a) (C_Expr a)
  deriving (Show, Functor, Foldable, Traversable)
makeBound ''C_Expr

cc :: Ord a => Expr a -> C_Expr a
cc = fst . go
  where
    go :: Ord a => Expr a -> (C_Expr a, [a])
    go ex =
      case ex of
        Var a -> (C_Var a, [a])
        UInt64 a -> (C_UInt64 a, [])
        Add a b ->
          let
            (a', vs1) = go a
            (b', vs2) = go b
          in
            (C_Add a' b', vs1 `union` vs2)
        Mult a b ->
          let
            (a', vs1) = go a
            (b', vs2) = go b
          in
            (C_Mult a' b', vs1 `union` vs2)
        App a b ->
          let
            (a', vs1) = go a
            (b', vs2) = go b
          in
            (C_App a' b', vs1 `union` vs2)
        Lam a ->
          let
            (a', vs) = go $ fromScope a
            fvs = foldr (unvar (\_ -> id) (:)) [] vs
            v_map = Map.fromList $ zip fvs [0..]
          in
            ( C_Lam
                (C_Var <$> fvs)
                (a' >>=
                unvar
                  (\_ -> C_Bound)
                  (\v -> maybe undefined C_Env $ Map.lookup v v_map))
            , fvs
            )
