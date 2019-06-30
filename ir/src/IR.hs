{-# language DeriveGeneric #-}
{-# language GeneralizedNewtypeDeriving #-}
module IR
  ( Reg, sp, rv, Const(..), Val(..), Exp(..), Stmt(..), foldStmts
  , IR, genIR, add, mul, mov, alloc, store, load, load0, push, pop
  , icall, ret
  , ijump
  , comment
  )
where

import Control.Lens.Plated (Plated(..), gplate)
import Control.Monad.State (State, runState, gets, modify)
import Data.Word (Word64)
import GHC.Generics (Generic)
import Text.PrettyPrint.ANSI.Leijen (Pretty(..))

import qualified Text.PrettyPrint.ANSI.Leijen as Pretty

data Reg
  = Reg Word64
  | SP
  | RV
  deriving (Eq, Ord, Show, Generic)
instance Pretty Reg where
  pretty (Reg a) = Pretty.char '%' <> Pretty.int (fromIntegral a)
  pretty SP = Pretty.text "%sp"
  pretty RV = Pretty.text "%rv"

data Const
  = Unit
  | Null
  | W64 Word64
  deriving (Eq, Ord, Show, Generic)
instance Pretty Const where
  pretty Unit = Pretty.text "unit"
  pretty Null = Pretty.text "null"
  pretty (W64 a) = Pretty.int (fromIntegral a)

data Val = C Const | R Reg | F String
  deriving (Eq, Ord, Show, Generic)
instance Pretty Val where
  pretty (C a) = pretty a
  pretty (R a) = pretty a
  pretty (F a) = Pretty.char '"' <> Pretty.text a <> Pretty.char '"'

data Exp
 -- | `Alloc x`: allocate n words on the heap
  = Alloc Val
  -- | `Load x y`: load x'th word from y
  | Load Val Val
  -- | `Store x y`: store x at the y'th word in z
  | Store Val Val Val
  | Mov Val Reg
  | Add Val Val
  | Mul Val Val
  | Const Const
  | Push Val
  | Pop
  | ICall Val
  | Ret
  | IJump Val
  deriving (Eq, Ord, Show, Generic)
instance Pretty Exp where
  pretty e =
    case e of
      Alloc a -> Pretty.text "alloc " <> pretty a
      Load a b -> Pretty.hsep [Pretty.text "load", pretty a, pretty b]
      Store a b c ->
        Pretty.hsep [Pretty.text "store", pretty a, pretty b, pretty c]
      Mov a b -> Pretty.hsep [Pretty.text "mov", pretty a, pretty b]
      Add a b -> Pretty.hsep [Pretty.text "add", pretty a, pretty b]
      Mul a b -> Pretty.hsep [Pretty.text "mul", pretty a, pretty b]
      Const a -> pretty a
      Push a -> Pretty.text "push " <> pretty a
      Pop -> Pretty.text "pop"
      ICall a -> Pretty.text "icall " <> pretty a
      Ret -> Pretty.text "ret"
      IJump a -> Pretty.text "ijump " <> pretty a

data Stmt
  = Pure Val
  | Bind Reg Exp Stmt
  | Seq Exp Stmt
  | Comment String Stmt
  deriving (Show, Generic)
instance Pretty Stmt where
  pretty (Pure a) = Pretty.text "pure " <> pretty a
  pretty (Bind a b c) =
    Pretty.hsep [pretty a, Pretty.char '=', pretty b <> Pretty.char ';'] Pretty.<$>
    pretty c
  pretty (Seq a b) =
    (pretty a <> Pretty.char ';') Pretty.<$>
    pretty b
  pretty (Comment a b) =
    Pretty.text "## " <> pretty a Pretty.<$>
    pretty b

foldStmts ::
  (Val -> r) ->
  (Reg -> Exp -> r -> r) ->
  (Exp -> r -> r) ->
  (String -> r -> r) ->
  Stmt -> r
foldStmts f _ _ _ (Pure a) = f a
foldStmts f g h i (Bind a b c) = g a b (foldStmts f g h i c)
foldStmts f g h i (Seq a b) = h a (foldStmts f g h i b)
foldStmts f g h i (Comment a b) = i a (foldStmts f g h i b)

instance Plated Stmt where; plate = gplate

data S = S { sRegs :: Word64, sCode :: Stmt -> Stmt }

newtype IR a = IR (State S a)
  deriving (Functor, Applicative, Monad)

nextReg :: IR Reg
nextReg = IR $ do
  r <- gets sRegs
  Reg r <$ modify (\s -> s { sRegs = sRegs s + 1 })

sp :: Reg
sp = SP

rv :: Reg
rv = RV

bind :: Exp -> IR Reg
bind e = do
  r <- nextReg
  r <$ IR (modify $ \s -> s { sCode = sCode s . Bind r e })

comment :: String -> IR ()
comment str = IR $ modify (\s -> s { sCode = sCode s . Comment str })

add :: Val -> Val -> IR Reg
add a b = bind $ Add a b

mul :: Val -> Val -> IR Reg
mul a b = bind $ Mul a b

store :: Val -> Val -> Val -> IR Reg
store a b c = bind $ Store a b c

mov :: Val -> Reg -> IR Reg
mov a b = bind $ Mov a b

push :: Val -> IR Reg
push = bind . Push

icall :: Val -> IR Reg
icall = bind . ICall

ret :: IR Reg
ret = bind Ret

pop :: IR Reg
pop = bind Pop

load :: Val -> Val -> IR Reg
load a b = bind $ Load a b

load0 :: Val -> IR Reg
load0 = load (C $ W64 0)

ijump :: Val -> IR Reg
ijump = bind . IJump


alloc :: Val -> IR Reg
alloc a = bind $ Alloc a

genIR :: IR Val -> Stmt
genIR (IR a) = let (v, s) = runState a (S 0 id) in sCode s (Pure v)
