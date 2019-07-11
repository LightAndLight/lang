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
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import Data.Word (Word64)

import qualified Data.Text as Text

import Core (Core)
import Core.Type (Kind)
import qualified Core
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
  Core ty tm ->
  m (Closure ty tm)
trans ex =
  fst <$>
  go (Var . F) pure ex
  where
    go ::
      forall a b.
      Eq b =>
      (b -> Closure ty (Var LVar tm)) ->
      (a -> m ty) ->
      Core a b ->
      m (Closure ty b, [b])
    go _ _ (Core.Var a) = pure (Var a, [a])
    go f g (Core.AppType a _) = go f g a
    go f g (Core.AbsType mn _ a) =
      go
        f
        (unvar
           (\() -> throwError . ArgumentAbstractKind $ fromMaybe "<unnamed>" mn) g)
        (fromBiscopeL a)
    go f g (Core.Lam _ _ kin kout a) = do
      rec
        let
          vs' = foldr (unvar (const id) (:)) [] vs
          replace =
            unvar
              (\_ -> Var $ B LArg)
              (\b -> maybe (f b) (\ix -> Proj (fromIntegral ix) (Var $ B LEnv)) $ elemIndex b vs')
        (a', vs) <- go replace g $ fromBiscopeR a
      n <- freshName
      kin' <- traverse g kin
      kout' <- traverse g kout
      tell [FunDef n kin' kout' . toScope $ a' >>= replace]
      pure (Closure (Name n) (Product $ Var <$> vs') kin' kout', vs')
    go f g (Core.App a b bk abk) = do
      (a', vs1) <- go f g a
      (b', vs2) <- go f g b
      bk' <- traverse g bk
      abk' <- traverse g abk
      pure (Unpack a' (toScope $ App (Var $ B Fst) (Var $ B Snd) (F <$> b')) bk' abk', vs1 `union` vs2)
    go f g (Core.Bin o a b) = do
      (a', vs1) <- go f g a
      (b', vs2) <- go f g b
      pure (Bin o a' b', vs1 `union` vs2)
    go _ _ (Core.UInt64 a) = pure (UInt64 a, [])

transDef ::
  forall ty tm m.
  ( MonadState [Text] m
  , MonadWriter [FunDef ty tm] m
  , MonadError ClosureError m
  , MonadFix m
  , Eq tm
  ) =>
  Core.Def ty tm ->
  m (ValDef ty tm)
transDef (Core.Def name tm) =
  ValDef name <$> trans tm

transDefs ::
  ( MonadState [Text] m
  , MonadWriter [FunDef ty tm] m
  , MonadError ClosureError m
  , MonadFix m
  , Eq tm
  ) =>
  [Core.Def ty tm] ->
  m [ValDef ty tm]
transDefs [] = pure []
transDefs (d:ds) =
  (:) <$> transDef d <*> transDefs ds

transProgram ::
  Eq tm =>
  ([Core.Def ty tm], Core ty tm) ->
  Either ClosureError ([FunDef ty tm], [ValDef ty tm], Closure ty tm)
transProgram (ds, tm) =
  runExcept $ do
    ((vds'', tm''), fds'') <-
      flip evalStateT (Text.pack . ('f' :) . show <$> [0::Int ..]) .
      runWriterT $ do
        tm' <- trans tm
        ds' <- transDefs ds
        pure (ds', tm')
    pure (fds'', vds'', tm'')
