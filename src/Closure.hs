{-# language BangPatterns #-}
{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language FlexibleContexts, RecursiveDo, ScopedTypeVariables #-}
{-# language OverloadedStrings #-}
{-# language StandaloneDeriving #-}
{-# language TemplateHaskell #-}
module Closure where

import Biscope (fromBiscopeR, fromBiscopeL)
import Bound.Scope.Simple (Scope, toScope)
import Bound.TH (makeBound)
import Bound.Var (Var(..), unvar)
import Control.Monad.Fix (MonadFix)
import Control.Monad.Except (MonadError, runExcept, throwError)
import Control.Monad.State (MonadState, evalStateT, get, put)
import Control.Monad.Writer (MonadWriter, runWriterT, tell)
import Data.Deriving (deriveEq1, deriveShow1)
import Data.Functor.Classes (eq1, showsPrec1)
import Data.List (elemIndex, union)
import Data.Maybe (fromJust, fromMaybe)
import Data.Text (Text)
import Data.Word (Word64)

import qualified Data.Map as Map
import qualified Data.Text as Text

import Core (Core)
import Core.Type (Kind)
import qualified Core
import qualified Core.Type as Core
import Operators (Op)

data Pos = Fst | Snd
  deriving (Eq, Show)

data Closure ty tm
  = Var tm
  | UInt64 !Word64
  | Name Text
  | Product [Closure ty tm]
  | Proj !Word64 (Closure ty tm)
  | Closure (Closure ty tm) (Closure ty tm) (Kind ty) (Kind ty)
  | Unpack (Closure ty tm) (Scope Pos (Closure ty) tm) (Kind ty) (Kind ty)
  | App (Closure ty tm) (Closure ty tm) (Closure ty tm)
  | Bin Op (Closure ty tm) (Closure ty tm)
  deriving (Functor, Foldable, Traversable)
makeBound ''Closure
deriveEq1 ''Closure
deriveShow1 ''Closure
instance (Eq ty, Eq tm) => Eq (Closure ty tm) where; (==) = eq1
instance (Show ty, Show tm) => Show (Closure ty tm) where; showsPrec = showsPrec1

data LVar = LEnv | LArg
  deriving (Eq, Show)

data FunDef ty tm
  = FunDef
  { fName :: Text
  , fInKind :: Kind ty
  , fOutKind :: Kind ty
  , fBody :: Scope LVar (Closure ty) tm
  }
  deriving (Eq, Show, Functor, Foldable, Traversable)

data ValDef ty tm = ValDef tm (Closure ty tm)
  deriving (Eq, Show, Functor, Foldable, Traversable)

freshName :: MonadState [a] m => m a
freshName = do
  s <- get
  case s of
    s' : ss' -> s' <$ put ss'
    [] -> undefined

data ClosureError
  = ArgumentAbstractKind Text
  deriving (Eq, Show)

trans ::
  forall ty tm m.
  ( MonadState [Text] m
  , MonadWriter [FunDef ty tm] m
  , MonadFix m
  , MonadError ClosureError m
  , Eq tm
  ) =>
  (tm -> Core.Type ty) ->
  (ty -> Core.Kind ty) ->
  Core ty tm ->
  m (Closure ty tm)
trans ts ks ex =
  fst <$>
  go ts ks (Var . F) pure ex
  where
    go ::
      forall x y.
      Eq y =>
      (y -> Core.Type x) ->
      (x -> Core.Kind x) ->
      (y -> Closure ty (Var LVar tm)) ->
      (x -> m ty) ->
      Core x y ->
      m (Closure ty y, [y])
    go _ _ _ _ (Core.Var a) = pure (Var a, [a])
    go typing kinding f g (Core.AppType a _) = go typing kinding f g a
    go typing kinding f g (Core.AbsType mn k a) =
      go
        (fmap F . typing)
        (unvar (\() -> F <$> k) (fmap F . kinding))
        f
        (unvar
           (\() -> throwError . ArgumentAbstractKind $ fromMaybe "<unnamed>" mn) g)
        (fromBiscopeL a)
    go typing kinding f g (Core.Lam (Core.LamInfo kin kout _ _) _ t a) = do
      rec
        let
          vs' = foldr (unvar (const id) (:)) [] vs
          replace =
            unvar
              (\_ -> Var $ B LArg)
              (\b -> maybe (f b) (\ix -> Proj (fromIntegral ix) (Var $ B LEnv)) $ elemIndex b vs')
        (a', vs) <- go (unvar (\() -> t) typing) kinding replace g $ fromBiscopeR a
      n <- freshName
      kin' <- traverse g kin
      kout' <- traverse g kout
      tell [FunDef n kin' kout' . toScope $ a' >>= replace]
      pure (Closure (Name n) (Product $ Var <$> vs') kin' kout', vs')
    go typing kinding f g (Core.App (Core.AppInfo bk abk) a b) = do
      (a', vs1) <- go typing kinding f g a
      (b', vs2) <- go typing kinding f g b
      bk' <- traverse g bk
      abk' <- traverse g abk
      pure (Unpack a' (toScope $ App (Var $ B Fst) (Var $ B Snd) (F <$> b')) bk' abk', vs1 `union` vs2)
    go typing kinding f g (Core.Bin o a b) = do
      (a', vs1) <- go typing kinding f g a
      (b', vs2) <- go typing kinding f g b
      pure (Bin o a' b', vs1 `union` vs2)
    go _ _ _ _ (Core.UInt64 a) = pure (UInt64 a, [])

transDef ::
  forall ty tm m.
  ( MonadState [Text] m
  , MonadWriter [FunDef ty tm] m
  , MonadError ClosureError m
  , MonadFix m
  , Eq tm
  ) =>
  (tm -> Core.Type ty) ->
  (ty -> Core.Kind ty) ->
  Core.Def ty tm ->
  m (ValDef ty tm)
transDef typing kinding (Core.Def name tm _) =
  ValDef name <$> trans typing kinding tm

transDefs ::
  ( MonadState [Text] m
  , MonadWriter [FunDef ty tm] m
  , MonadError ClosureError m
  , MonadFix m
  , Eq tm
  ) =>
  (tm -> Core.Type ty) ->
  (ty -> Core.Kind ty) ->
  [Core.Def ty tm] ->
  m [ValDef ty tm]
transDefs _ _ [] = pure []
transDefs typing kinding (d:ds) =
  (:) <$> transDef typing kinding d <*> transDefs typing kinding ds

transProgram ::
  Ord tm =>
  (ty -> Core.Kind ty) ->
  ([Core.Def ty tm], Core ty tm) ->
  Either ClosureError ([FunDef ty tm], [ValDef ty tm], Closure ty tm)
transProgram kinding (ds, tm) =
  runExcept $ do
    ((vds'', tm''), fds'') <-
      flip evalStateT (Text.pack . ('f' :) . show <$> [0::Int ..]) .
      runWriterT $ do
        let
          typing n =
            fromJust . Map.lookup n $
            foldr (\(Core.Def name _ ty) -> Map.insert name ty) mempty ds
        ds' <- transDefs typing kinding ds
        tm' <- trans typing kinding tm
        pure (ds', tm')
    pure (fds'', vds'', tm'')
