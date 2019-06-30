{-# language DeriveGeneric #-}
{-# language GeneralizedNewtypeDeriving #-}
module IR
  ( Reg, sp, Const(..), Val(..), Exp(..), Stmt(..), foldStmts
  , IR, genIR, add, mul, mov, alloc, store, load, load0
  , icall, ret
  , comment
  )
where

import Control.Lens.Plated (Plated(..), gplate)
import Control.Monad.State (State, runState, gets, modify)
import Data.Foldable (fold)
import Data.List (intersperse)
import Data.Word (Word64)
import GHC.Generics (Generic)
import Text.PrettyPrint.ANSI.Leijen (Pretty(..), Doc)

import qualified Text.PrettyPrint.ANSI.Leijen as Pretty

data Reg
  = Reg Word64
  | SP
  deriving (Eq, Ord, Show, Generic)
instance Pretty Reg where
  pretty (Reg a) = Pretty.char '%' <> Pretty.int (fromIntegral a)
  pretty SP = Pretty.text "%sp"

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
  | ICall Val [Val]
  | Ret Val
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
      ICall a bs ->
        Pretty.text "icall " <>
        pretty a <>
        Pretty.brackets (fold . intersperse (Pretty.text ", ") $ pretty <$> bs)
      Ret a -> Pretty.text "ret " <> pretty a

stmtRest :: Doc -> Stmt -> Doc
stmtRest body rest =
  case rest of
    Empty -> body
    _ -> body Pretty.<$> pretty rest

data Stmt
  = Empty
  | Pure Val
  | Bind Reg Exp Stmt
  | Seq Exp Stmt
  | Comment String Stmt
  deriving (Show, Generic)
instance Pretty Stmt where
  pretty Empty = mempty
  pretty (Pure a) = Pretty.text "pure " <> pretty a
  pretty (Bind a b c) =
    stmtRest
      (Pretty.hsep [pretty a, Pretty.char '=', pretty b <> Pretty.char ';'])
      c
  pretty (Seq a b) =
    stmtRest (pretty a <> Pretty.char ';') b
  pretty (Comment a b) =
    stmtRest (Pretty.text "## " <> pretty a) b

foldStmts ::
  r ->
  (Val -> r) ->
  (Reg -> Exp -> r -> r) ->
  (Exp -> r -> r) ->
  (String -> r -> r) ->
  Stmt -> r
foldStmts e _ _ _ _ Empty = e
foldStmts _ f _ _ _ (Pure a) = f a
foldStmts e f g h i (Bind a b c) = g a b (foldStmts e f g h i c)
foldStmts e f g h i (Seq a b) = h a (foldStmts e f g h i b)
foldStmts e f g h i (Comment a b) = i a (foldStmts e f g h i b)

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

bind :: Exp -> IR Reg
bind e = do
  r <- nextReg
  r <$ IR (modify $ \s -> s { sCode = sCode s . Bind r e })

expr :: Exp -> IR ()
expr e = IR $ modify (\s -> s { sCode = sCode s . Seq e })

comment :: String -> IR ()
comment str = IR $ modify (\s -> s { sCode = sCode s . Comment str })

add :: Val -> Val -> IR Reg
add a b = bind $ Add a b

mul :: Val -> Val -> IR Reg
mul a b = bind $ Mul a b

store :: Val -> Val -> Val -> IR ()
store a b c = expr $ Store a b c

mov :: Val -> Reg -> IR Reg
mov a b = bind $ Mov a b

icall :: Val -> [Val] -> IR Reg
icall a = bind . ICall a

ret :: Val -> IR ()
ret = expr . Ret

load :: Val -> Val -> IR Reg
load a b = bind $ Load a b

load0 :: Val -> IR Reg
load0 = load (C $ W64 0)

alloc :: Val -> IR Reg
alloc a = bind $ Alloc a

genIR :: IR a -> Stmt
genIR (IR a) = let (_, s) = runState a (S 0 id) in sCode s Empty