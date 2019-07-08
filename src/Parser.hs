{-# language OverloadedLists #-}
module Parser where

import Bound.Scope.Simple (abstract1)
import Control.Applicative ((<|>), some)
import Data.Text (Text)
import Text.Trifecta
  ( TokenParsing, IdentifierStyle(..)
  , char, lower, alphaNum
  )
import Text.Parser.Expression (Operator(..), Assoc(..), buildExpressionParser)

import qualified Text.Trifecta as Trifecta
import qualified Text.Parser.Token.Highlight as Highlight

import Syntax
import Operators (Op(..))

ident :: (Monad m, TokenParsing m) => m Text
ident =
  Trifecta.ident $
  IdentifierStyle
  { _styleName = "ident"
  , _styleStart = lower
  , _styleLetter = alphaNum
  , _styleReserved = []
  , _styleHighlight = Highlight.Identifier
  , _styleReservedHighlight = Highlight.ReservedIdentifier
  }

expr :: (Monad m, TokenParsing m) => m (Syntax Text)
expr = lam <|> compound
  where
    lam = (\x -> Lam (Just x) . abstract1 x) <$ char '\\' <*> ident <*> expr
    app = foldl1 App <$> some atom
    opTable =
      [ [Infix (Bin Mult <$ char '*') AssocLeft]
      , [Infix (Bin Add <$ char '+') AssocLeft]
      ]
    compound = buildExpressionParser opTable app
    atom =
      Trifecta.parens expr <|>
      Natural <$> Trifecta.decimal