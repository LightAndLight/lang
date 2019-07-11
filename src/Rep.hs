module Rep where

data Rep = RPtr | RI64 | RList [Rep]
  deriving (Eq, Show)