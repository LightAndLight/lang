{-# language BangPatterns #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language LambdaCase #-}
module Codegen where

import Bound.Scope.Simple (fromScope)
import Bound.Var (unvar)
import Data.Foldable (for_)
import Data.Map (Map)
import Data.Word (Word64)
import IR (IR)
import Text.PrettyPrint.ANSI.Leijen (Pretty(..))

import qualified Data.Map as Map
import qualified IR
import qualified Text.PrettyPrint.ANSI.Leijen as Pretty

import Syntax

tag :: String -> IR a -> IR a
tag desc ma =
  IR.comment ("begin: " <> desc) *>
  ma <*
  IR.comment ("end: " <> desc)

cg_def :: (a -> IR IR.Val) -> LDef a -> Map String IR.Stmt
cg_def var (LDef ln lb) =
  Map.singleton ln . IR.genIR $ do
    a' <- cg_expr
      (unvar
        (\case
            LEnv ->
              tag "access env" $
              IR.R <$> IR.load (IR.C $ IR.W64 2) (IR.R IR.sp)
            LArg ->
              tag "access arg" $
              IR.R <$> IR.load (IR.C $ IR.W64 1) (IR.R IR.sp))
        var)
      (fromScope lb)
    IR.ret a'

cg_expr :: (a -> IR IR.Val) -> LL a -> IR IR.Val
cg_expr = go
  where
    go :: (a -> IR IR.Val) -> LL a -> IR IR.Val
    go var ex =
      case ex of
        LVar a -> var a
        LName a -> pure $ IR.F a
        LUInt64 a -> pure $ IR.C (IR.W64 a)
        LProduct as -> do
          let las = length as
          loc <-
            tag "allocate product" $
            IR.alloc (IR.C . IR.W64 $ fromIntegral las)
          tag "allocate product elements" $
            for_ (zip [0::Word64 ..] as) $ \(n, a) -> do
              a' <- go var a
              IR.store a' (IR.C $ IR.W64 n) (IR.R loc)
          pure $ IR.R loc
        LProj n a -> do
          a' <- go var a
          IR.R <$> IR.load (IR.C $ IR.W64 n) a'
        LBin o a b -> do
          va <- go var a
          vb <- go var b
          case o of
            Add -> IR.R <$> IR.add va vb
            Mult -> IR.R <$> IR.mul va vb
        LApp f e x -> do
          f' <- go var f
          e' <- go var e
          x' <- go var x
          IR.R <$> IR.icall f' [e', x']
        LClosure a b -> do
          loc <- tag "allocate closure" $ IR.alloc (IR.C $ IR.W64 2)
          tag "pack code" $ do
            a' <- go var a
            IR.store a' (IR.C $ IR.W64 0) (IR.R loc)
          tag "pack env" $ do
            b' <- go var b
            IR.store b' (IR.C $ IR.W64 1) (IR.R loc)
          pure $ IR.R loc
        LUnpack a b -> do
          a' <- go var a
          a1 <- IR.R <$> IR.load (IR.C $ IR.W64 0) a'
          a2 <- IR.R <$> IR.load (IR.C $ IR.W64 1) a'
          go
            (unvar (\case; Fst -> pure a1; Snd -> pure a2) var)
            (fromScope b)

newtype Defs a = Defs { unDefs :: Map String a }
  deriving (Functor, Foldable, Show)

instance Pretty a => Pretty (Defs a) where
  pretty (Defs a) =
    Map.foldrWithKey
      (\k v rest ->
         Pretty.text k <> Pretty.text " {" Pretty.<$>
         Pretty.indent 2 (pretty v) Pretty.<$>
         Pretty.char '}' Pretty.<$> mempty Pretty.<$>
         rest)
      mempty
      a

cg :: (a -> IR IR.Val) -> (LL a, [LDef a]) -> (IR.Stmt, Defs IR.Stmt)
cg var (val, ds) = (val', Defs ds')
  where
    val' = IR.genIR $ cg_expr var val
    ds' = foldMap (cg_def var) ds