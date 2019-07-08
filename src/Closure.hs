{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language FlexibleContexts, RecursiveDo, ScopedTypeVariables #-}
{-# language StandaloneDeriving #-}
{-# language TemplateHaskell #-}
module Closure where

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

import Core (Core)
import qualified Core
import Operators (Op)

data Pos = Fst | Snd
  deriving (Eq, Show)

data Closure a
  = Var a
  | UInt64 !Word64
  | Name String
  | Product [Closure a]
  | Proj !Word64 (Closure a)
  | Closure (Closure a) (Closure a)
  | Unpack (Closure a) (Scope Pos Closure a)
  | App (Closure a) (Closure a) (Closure a)
  | Bin Op (Closure a) (Closure a)
  deriving (Functor, Foldable, Traversable)
makeBound ''Closure
deriveEq1 ''Closure
deriveShow1 ''Closure
instance Eq a => Eq (Closure a) where; (==) = eq1
instance Show a => Show (Closure a) where; showsPrec = showsPrec1

data LVar = LEnv | LArg
  deriving (Eq, Show)

data LDef a = LDef { lName :: String, lBody :: Scope LVar Closure a }
  deriving (Eq, Show, Functor, Foldable, Traversable)

freshName :: MonadState [a] m => m a
freshName = do
  s <- get
  case s of
    s' : ss' -> s' <$ put ss'
    [] -> undefined

trans :: forall a. Eq a => Core a -> (Closure a, [LDef a])
trans ex = (val, defs)
  where
    ((val, _), defs) = runWriter $ evalStateT (go (Var . F) ex) (('f' :) . show <$> [0::Int ..])

    go ::
      forall b m.
      (Eq b, MonadWriter [LDef a] m, MonadState [String] m, MonadFix m) =>
      (b -> Closure (Var LVar a)) ->
      Core b -> m (Closure b, [b])
    go _ (Core.Var a) = pure (Var a, [a])
    go f (Core.Lam _ a) = do
      rec
        let
          vs' = foldr (unvar (const id) (:)) [] vs
          replace =
            unvar
              (\_ -> Var $ B LArg)
              (\b -> maybe (f b) (\ix -> Proj (fromIntegral ix) (Var $ B LEnv)) $ elemIndex b vs')
        (a', vs) <- go replace $ fromScope a
      n <- freshName
      tell [LDef n $ toScope $ a' >>= replace]
      pure (Closure (Name n) (Product $ Var <$> vs'), vs')
    go f (Core.App a b) = do
      (a', vs1) <- go f a
      (b', vs2) <- go f b
      pure (Unpack a' (toScope $ App (Var $ B Fst) (Var $ B Snd) (F <$> b')), vs1 `union` vs2)
    go f (Core.Bin o a b) = do
      (a', vs1) <- go f a
      (b', vs2) <- go f b
      pure (Bin o a' b', vs1 `union` vs2)
    go _ (Core.UInt64 a) = pure (UInt64 a, [])