{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language FlexibleContexts, RecursiveDo, ScopedTypeVariables #-}
{-# language StandaloneDeriving #-}
{-# language TemplateHaskell #-}
module Closure where

import Biscope (fromBiscopeR, fromBiscopeL)
import Bound.Scope.Simple (Scope, toScope)
import Bound.TH (makeBound)
import Bound.Var (Var(..), unvar)
import Control.Monad.Fix (MonadFix)
import Control.Monad.State (MonadState, evalState, get, put)
import Control.Monad.Writer (MonadWriter, runWriterT, tell)
import Data.Deriving (deriveEq1, deriveShow1)
import Data.Functor.Classes (eq1, showsPrec1)
import Data.List (elemIndex, union)
import Data.Text (Text)
import Data.Word (Word64)

import qualified Data.Text as Text

import Core (Core)
import qualified Core
import Operators (Op)

data Pos = Fst | Snd
  deriving (Eq, Show)

data Closure a
  = Var a
  | UInt64 !Word64
  | Name Text
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

data Def tm
  = GenDef Text (Scope LVar Closure tm)
  | UserDef tm (Closure tm)
  deriving (Eq, Show, Functor, Foldable, Traversable)

freshName :: MonadState [a] m => m a
freshName = do
  s <- get
  case s of
    s' : ss' -> s' <$ put ss'
    [] -> undefined

trans ::
  forall ty tm m.
  (MonadState [Text] m, MonadFix m, Eq tm) =>
  Core ty tm -> m ([Def tm], Closure tm)
trans ex = do
  ((val, _), defs) <- runWriterT $ go (Var . F) ex
  pure (defs, val)
  where

    go ::
      forall x b n.
      (Eq b, MonadWriter [Def tm] n, MonadState [Text] n, MonadFix n) =>
      (b -> Closure (Var LVar tm)) ->
      Core x b -> n (Closure b, [b])
    go _ (Core.Var a) = pure (Var a, [a])
    go f (Core.AppType a _) = go f a
    go f (Core.AbsType _ _ a) = go f $ fromBiscopeL a
    go f (Core.Lam _ _ a) = do
      rec
        let
          vs' = foldr (unvar (const id) (:)) [] vs
          replace =
            unvar
              (\_ -> Var $ B LArg)
              (\b -> maybe (f b) (\ix -> Proj (fromIntegral ix) (Var $ B LEnv)) $ elemIndex b vs')
        (a', vs) <- go replace $ fromBiscopeR a
      n <- freshName
      tell [GenDef n $ toScope $ a' >>= replace]
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

transDef ::
  forall ty tm m.
  (MonadState [Text] m, MonadFix m, Eq tm) =>
  Core.Def ty tm -> m [Def tm]
transDef (Core.Def name tm) = do
  (ds, tm') <- trans tm
  pure $ UserDef name tm' : ds

transDefs ::
  (MonadState [Text] m, MonadFix m, Eq tm) =>
  [Core.Def ty tm] -> m [Def tm]
transDefs [] = pure []
transDefs (d:ds) = (++) <$> transDef d <*> transDefs ds

transProgram :: Eq tm => ([Core.Def ty tm], Core ty tm) -> ([Def tm], Closure tm)
transProgram (ds, tm) =
  flip evalState (Text.pack . ('f' :) . show <$> [0::Int ..]) $ do
    (ds1, tm') <- trans tm
    ds2 <- transDefs ds
    pure (ds2 <> ds1, tm')
