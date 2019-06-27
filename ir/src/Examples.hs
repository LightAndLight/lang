module Examples where

import IR

addStuff :: IR Val
addStuff = do
  r1 <- add (C $ W64 10) (C $ W64 12)
  r2 <- add (R r1) (C $ W64 20)
  return $ R r2

prog :: Val -> Val -> IR Val
prog a b = do
  r1 <- load a
  r2 <- load b
  r3 <- add (R r1) (R r2)
  r4 <- load a
  r5 <- load b
  r6 <- add (R r4) (R r5)
  R <$> mul (R r3) (R r6)

