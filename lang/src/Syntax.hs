{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language StandaloneDeriving #-}
{-# language FlexibleContexts, RecursiveDo, ScopedTypeVariables #-}
{-# language TemplateHaskell #-}
module Syntax where

import Bound.Scope.Simple (Scope, fromScope, toScope)
import Bound.TH (makeBound)
import Bound.Var (Var(..), unvar)
import Control.Monad.Fix (MonadFix)
import Control.Monad.State (MonadState, evalStateT, get, put)
import Control.Monad.Writer (MonadWriter, runWriter, tell)
import Data.Deriving (deriveEq1, deriveShow1)
import Data.Functor.Classes (eq1, showsPrec1)
import Data.List (elemIndex, union)
import Data.Word (Word64)

data Op = Add | Mult deriving (Eq, Show)

data Exp a
  = Var a
  | UInt64 !Word64
  | Bin Op (Exp a) (Exp a)
  | Lam (Scope () Exp a)
  | App (Exp a) (Exp a)
  deriving (Functor, Foldable, Traversable)
makeBound ''Exp
deriveEq1 ''Exp
deriveShow1 ''Exp
instance Eq a => Eq (Exp a) where; (==) = eq1
instance Show a => Show (Exp a) where; showsPrec = showsPrec1

data Pos = Fst | Snd
  deriving (Eq, Show)

data LL a
  = LVar a
  | LUInt64 !Word64
  | LName String
  | LProduct [LL a]
  | LProj !Word64 (LL a)
  | LPack (LL a) (LL a)
  | LUnpack (LL a) (Scope Pos LL a)
  | LApp (LL a) (LL a) (LL a)
  | LBin Op (LL a) (LL a)
  deriving (Functor, Foldable, Traversable)
makeBound ''LL
deriveEq1 ''LL
deriveShow1 ''LL
instance Eq a => Eq (LL a) where; (==) = eq1
instance Show a => Show (LL a) where; showsPrec = showsPrec1

data LVar = LEnv Int | LArg
  deriving (Eq, Show)

lvar :: (Int -> r) -> r -> LVar -> r
lvar f _ (LEnv a) = f a
lvar _ a LArg = a

data LDef a = LDef { lName :: String, lBody :: Scope LVar LL a }
  deriving (Eq, Show, Functor, Foldable, Traversable)

freshName :: MonadState [a] m => m a
freshName = do
  s <- get
  case s of
    s' : ss' -> s' <$ put ss'
    [] -> undefined

trans :: forall a. Eq a => Exp a -> (LL a, [LDef a])
trans ex = (val, defs)
  where
    ((val, _), defs) = runWriter $ evalStateT (go F ex) (('f' :) . show <$> [0::Int ..])

    go ::
      forall b m.
      (Eq b, MonadWriter [LDef a] m, MonadState [String] m, MonadFix m) =>
      (b -> Var LVar a) ->
      Exp b -> m (LL b, [b])
    go _ (Var a) = pure (LVar a, [a])
    go f (Lam a) = do
      rec
        let replace = unvar (\_ -> B LArg) (\b -> maybe (f b) (B . LEnv) $ elemIndex b vs')
        (a', vs) <- go replace $ fromScope a
        let vs' = foldr (unvar (const id) (:)) [] vs
      n <- freshName
      tell [LDef n $ toScope $ replace <$> a']
      pure (LPack (LName n) (LProduct $ LVar <$> vs'), vs')
    go f (App a b) = do
      (a', vs1) <- go f a
      (b', vs2) <- go f b
      pure (LUnpack a' (toScope $ LApp (LVar $ B Fst) (LVar $ B Snd) (F <$> b')), vs1 `union` vs2)
    go f (Bin o a b) = do
      (a', vs1) <- go f a
      (b', vs2) <- go f b
      pure (LBin o a' b', vs1 `union` vs2)
    go _ (UInt64 a) = pure (LUInt64 a, [])