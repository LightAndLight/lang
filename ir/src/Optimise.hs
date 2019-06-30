{-# language FlexibleContexts #-}
{-# language LambdaCase #-}
{-# language TypeApplications #-}
module Optimise where

import Control.Applicative ((<|>), empty)
import Control.Lens.Traversal (traverseOf)
import Control.Monad (guard)
import Control.Monad.Trans.Maybe (MaybeT(..), runMaybeT)
import Control.Monad.State (MonadState, evalState, gets, modify)
import Control.Monad.Writer (runWriterT, tell)
import Data.Foldable (asum)
import Data.Generics.Product.Types (types)
import Data.Map (Map)
import Data.Monoid (Any(..))

import qualified Data.Map as Map

import IR

fold_constants :: Monad m => Exp -> MaybeT m Exp
fold_constants e =
  case e of
    Add (C (W64 a)) (C (W64 b)) -> pure $ Const (W64 $ a + b)
    Mul (C (W64 a)) (C (W64 b)) -> pure $ Const (W64 $ a * b)
    _ -> empty

alloc_0_null :: Monad m => Exp -> MaybeT m Exp
alloc_0_null (Alloc (C (W64 0))) = pure $ Const Null
alloc_0_null _ = empty

mov_id :: Monad m => Exp -> MaybeT m Exp
mov_id (Mov a b) = Const Unit <$ guard (a == R b)
mov_id _ = empty

inline_constants_exp :: MonadState (Map Reg Const) m => Exp -> MaybeT m Exp
inline_constants_exp e = do
  (a, Any change) <-
    runWriterT $
    traverseOf
      (types @Val)
      (\case
         R r -> do
           m_c <- gets (Map.lookup r)
           case m_c of
             Nothing -> pure $ R r
             Just c -> C c <$ tell (Any True)
         v -> pure v)
      e
  a <$ guard change

rewrite_exps ::
  Monad m =>
  (Exp -> MaybeT m Exp) -> Stmt -> MaybeT m Stmt
rewrite_exps f st =
  case st of
    Bind n e rest ->
      (\e' -> Bind n e' rest) <$> f e <|>
      Bind n e <$> rewrite_exps f rest
    Seq a b ->
      (\a' -> Seq a' b) <$> f a <|>
      Seq a <$> rewrite_exps f b
    Comment a b -> Comment a <$> rewrite_exps f b
    Pure{} -> empty

inline_constants_stmt ::
  MonadState (Map Reg Const) m => Stmt -> MaybeT m Stmt
inline_constants_stmt st =
  case st of
    Pure v ->
      case v of
        R r -> Pure . C <$> MaybeT (gets $ Map.lookup r)
        _ -> empty
    Bind n e rest ->
      case e of
        Const c -> rest <$ modify (Map.insert n c)
        _ -> Bind n e <$> inline_constants_stmt rest
    Seq e rest -> Seq e <$> inline_constants_stmt rest
    Comment s rest -> Comment s <$> inline_constants_stmt rest

optimise :: Stmt -> Stmt
optimise s =
  evalState
    (repeatedly (runMaybeT . do_many stmt_opts) s)
    mempty
  where
    repeatedly f x = maybe (pure x) (repeatedly f) =<< f x

    do_many as x = asum (($ x) <$> as)

    exp_opts =
      [ fold_constants
      , inline_constants_exp
      , alloc_0_null
      , mov_id
      ]

    stmt_opts =
      [ inline_constants_stmt
      , rewrite_exps (do_many exp_opts)
      ]
