{-# language DeriveGeneric #-}
{-# language GeneralizedNewtypeDeriving #-}
module IR
  ( Reg, Const(..), Val(..), Exp(..), Stmt(..), foldStmts
  , IR, genIR, add, mul, alloc, load
  )
where

import Control.Lens.Plated (Plated(..), gplate)
import Control.Monad.State (State, runState, gets, modify)
import Data.Word (Word64)
import GHC.Generics (Generic)

newtype Reg
  = Reg Word64
  deriving (Eq, Ord, Show, Generic)

data Const
  = W64 Word64
  deriving (Eq, Ord, Show, Generic)

data Val = C Const | R Reg
  deriving (Eq, Ord, Show, Generic)

data Exp
  = Alloc Val
  | Load Val
  | Store Val Val
  | Add Val Val
  | Mul Val Val
  | Const Const
  deriving (Eq, Ord, Show, Generic)

data Stmt
  = Pure Val
  | Bind Reg Exp Stmt
  deriving (Show, Generic)

foldStmts :: (Val -> r) -> (Reg -> Exp -> r -> r) -> Stmt -> r
foldStmts f _ (Pure a) = f a
foldStmts f g (Bind a b c) = g a b (foldStmts f g c)

instance Plated Stmt where; plate = gplate

data S = S { sRegs :: Word64, sCode :: Stmt -> Stmt }

newtype IR a = IR (State S a)
  deriving (Functor, Applicative, Monad)

nextReg :: IR Reg
nextReg = IR $ do
  r <- gets sRegs
  Reg r <$ modify (\s -> s { sRegs = sRegs s + 1 })

bind :: Exp -> IR Reg
bind e = do
  r <- nextReg
  r <$ IR (modify $ \s -> s { sCode = sCode s . Bind r e })

add :: Val -> Val -> IR Reg
add a b = bind $ Add a b

mul :: Val -> Val -> IR Reg
mul a b = bind $ Mul a b

load :: Val -> IR Reg
load a = bind $ Load a

alloc :: Val -> IR Reg
alloc a = bind $ Alloc a

genIR :: IR Val -> Stmt
genIR (IR a) = let (v, s) = runState a (S 0 id) in sCode s (Pure v)
