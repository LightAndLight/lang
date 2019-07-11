{-# language OverloadedLists #-}
{-# language OverloadedStrings #-}
{-# language RankNTypes #-}
module Parser where

import Biscope (abs1BiscopeR, abs1BiscopeL)
import Bound.Scope.Simple (abstract1)
import Control.Applicative ((<|>), some, many)
import Data.String (fromString)
import Data.Text (Text)
import Data.Text.Encoding (encodeUtf8)
import Text.Trifecta
  ( CharParsing, TokenParsing, IdentifierStyle(..)
  , lower, upper, alphaNum
  )
import Text.Parser.Expression (Operator(..), Assoc(..), buildExpressionParser)

import qualified Text.Trifecta as Trifecta
import qualified Text.Trifecta.Delta as Delta
import qualified Text.Parser.Token.Highlight as Highlight

import Operators (Op(..))
import Rep (Rep(..))
import Syntax
import Syntax.Type (Type(..))

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

atSymbol :: TokenParsing m => m Char
atSymbol = Trifecta.symbolic '@'

expr :: (Monad m, TokenParsing m) => m (Syntax Text Text)
expr = lambda <|> compound
  where
    lambda =
      either
        (\n -> Lam (Just n) . abs1BiscopeR n)
        (\(n, k) -> AbsType (Just n) k . abs1BiscopeL n) <$ Trifecta.symbolic '\\' <*>
      (Left <$> ident <|>
       Right <$ atSymbol <*>
       Trifecta.parens
         ((,) <$> ident <* Trifecta.colon <*> type_)) <* Trifecta.textSymbol "->" <*>
      expr

    app =
      foldl (\acc -> either (App acc) (AppType acc)) <$>
      atom <*>
      many (Left <$> atom <|> Right <$ atSymbol <*> tyAtom)

    opTable =
      [ [Infix (Bin Mult <$ Trifecta.symbolic '*') AssocLeft]
      , [Infix (Bin Add <$ Trifecta.symbolic '+') AssocLeft]
      ]

    compound = buildExpressionParser opTable app

    atom =
      Trifecta.parens expr <|>
      Natural <$> Trifecta.decimal

-- | Only use this for short strings
parse :: (forall m. (Monad m, TokenParsing m) => m a) -> FilePath -> Text -> Trifecta.Result a
parse m fn = Trifecta.runParser m (Delta.Directed (fromString fn) 0 0 0 0) . encodeUtf8

-- | Use this for files
parseFile :: (forall m. (Monad m, TokenParsing m) => m a) -> FilePath -> IO (Trifecta.Result a)
parseFile = Trifecta.parseFromFileEx