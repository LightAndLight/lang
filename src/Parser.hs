{-# language OverloadedLists #-}
{-# language OverloadedStrings #-}
module Parser where

import Biscope (abs1BiscopeR, abs1BiscopeL)
import Bound.Scope.Simple (abstract1)
import Control.Applicative ((<|>), some, many, liftA2)
import Data.Text (Text)
import Text.Trifecta
  ( CharParsing, TokenParsing, IdentifierStyle(..)
  , char, lower, upper, alphaNum
  )
import Text.Parser.Expression (Operator(..), Assoc(..), buildExpressionParser)

import qualified Text.Trifecta as Trifecta
import qualified Text.Parser.Token.Highlight as Highlight

import Core.Type (Type(..), Rep(..))
import Operators (Op(..))
import Syntax

identStyle :: CharParsing m => IdentifierStyle m
identStyle =
  IdentifierStyle
  { _styleName = "ident"
  , _styleStart = lower
  , _styleLetter = alphaNum
  , _styleReserved = ["forall", "pi"]
  , _styleHighlight = Highlight.Identifier
  , _styleReservedHighlight = Highlight.ReservedIdentifier
  }

ctorStyle :: CharParsing m => IdentifierStyle m
ctorStyle =
  IdentifierStyle
  { _styleName = "constructor"
  , _styleStart = upper
  , _styleLetter = alphaNum
  , _styleReserved = []
  , _styleHighlight = Highlight.Constructor
  , _styleReservedHighlight = Highlight.ReservedConstructor
  }


ident :: (Monad m, TokenParsing m) => m Text
ident = Trifecta.ident identStyle

ctor :: (Monad m, TokenParsing m) => m Text
ctor = Trifecta.ident ctorStyle

reservedI :: (Monad m, TokenParsing m) => Text -> m ()
reservedI = Trifecta.reserveText identStyle

reservedC :: (Monad m, TokenParsing m) => Text -> m ()
reservedC = Trifecta.reserveText ctorStyle

rep :: (Monad m, TokenParsing m) => m Rep
rep =
  RPtr <$ reservedC "RPtr" <|>
  RI64 <$ reservedC "RI64" <|>
  RList <$ Trifecta.runUnspaced (reservedC "RList") <*> Trifecta.brackets (many rep)

tyAtom :: (Monad m, TokenParsing m) => m (Type Text)
tyAtom =
  TVar <$> ident <|>
  TUInt64 <$ reservedC "UInt64" <|>
  TArr <$ reservedC "Arrow" <|>
  TRep <$> rep <|>
  TKRep <$ reservedC "Rep" <|>
  TKType <$ Trifecta.runUnspaced (reservedC "Type") <*> Trifecta.brackets Trifecta.decimal <|>
  Trifecta.parens type_

type_ :: (Monad m, TokenParsing m) => m (Type Text)
type_ =
  foldl1 TApp <$> some tyAtom

  <|>

  (\(n, k) -> TForall (Just n) k . abstract1 n) <$ reservedI "forall" <*>
  Trifecta.parens ((,) <$> ident <* Trifecta.colon <*> type_) <* Trifecta.dot <*>
  type_

  <|>

  (\(n, k) -> TKPi (Just n) k . abstract1 n) <$ reservedI "pi" <*>
  Trifecta.parens ((,) <$> ident <* Trifecta.colon <*> type_) <* Trifecta.dot <*>
  type_

expr :: (Monad m, TokenParsing m) => m (Syntax Text Text)
expr = lam <|> compound
  where
    lam =
      either
        (\n -> Lam (Just n) . abs1BiscopeR n)
        (\(n, k) -> AbsType (Just n) k . abs1BiscopeL n) <$ char '\\' <*>
      (Left <$> ident <|>
       Right <$ char '@' <*> liftA2 (,) ident (Trifecta.colon *> type_)) <*>
      expr

    app =
      foldl (\acc -> either (App acc) (AppType acc)) <$>
      atom <*>
      many (Left <$> atom <|> Right <$ char '@' <*> tyAtom)

    opTable =
      [ [Infix (Bin Mult <$ char '*') AssocLeft]
      , [Infix (Bin Add <$ char '+') AssocLeft]
      ]

    compound = buildExpressionParser opTable app

    atom =
      Trifecta.parens expr <|>
      Natural <$> Trifecta.decimal