{-# LANGUAGE TypeFamilies, FlexibleContexts, FlexibleInstances, DeriveDataTypeable #-}

{- | The various variables that "Syntax" uses.

   We make liberal use of trees that grow within the Amulet compiler,
   meaning we define a series of \"phases\" ('Parsed', 'Resolved',
   etc...) and use type families to change how we annotate syntax as
   progress through the compiler progresses.
-}
module Syntax.Var where

import Data.Text (Text)
import Data.Data

import Text.Pretty.Semantic

-- | The parsed phrase is used on the result of the parser, before
-- resolution occurs.
--
-- Variables are only aware of their name and we only annotate values
-- with their position in the original code.
newtype Parsed = Parsed Parsed deriving Data

-- | The resolved phrase is used after we have resolved variables, and
-- during desugaring.
--
-- We do not provide any additional annotations, but do uniquify
-- variables.
newtype Resolved = Resolved Resolved deriving Data

-- | The desugared phrase is used after we have resolved variables and
-- desugared terms.
newtype Desugared = Desugared Desugared deriving Data

-- | This is used after (and during) type checking, before we need to
-- lower to core.
--
-- We do not provide any additional information to variables. However,
-- all terms are now annotated with their type, which can be extracted if
-- needed.
newtype Typed = Typed Typed deriving Data

-- | An alias for resolved variables, this is considered the "default"
-- name, though should not be confused with the parsed variable
-- constructor.
type Name = Var Resolved

-- | A variable at a given phase of compilation.
type family Var p :: * where
  Var Parsed = VarParsed
  Var Resolved = VarResolved
  Var Desugared = VarResolved
  Var Typed = VarResolved

-- | Parsed variables are little more than identifiers: they do not have
-- a concept of scope.
newtype VarParsed = Name Text
  deriving (Eq, Show, Ord, Data)

-- | A unique identifier, used by resolved variables.
data Ident = Ident Text {-# UNPACK #-} !Int
  deriving (Show, Data)

instance Eq Ident where
  Ident _ x == Ident  _ y = x == y

instance Ord Ident where
  Ident _ x `compare` Ident _ y = x `compare` y

-- | A resolved variable. These no longer keep track of which module they
-- belong to, and thus simply hold a 'Text' value.
data VarResolved
  = TgName !Ident -- ^ A user-defined name
  | TgInternal Text -- ^ A variable provided by the compiler
  deriving (Data, Eq, Show, Ord)

instance Pretty VarParsed where
  pretty (Name v) = text v

instance Pretty Ident where
  pretty (Ident v i) = text v <> scomment (string "#" <> string (show i))

instance Pretty VarResolved where
  pretty (TgName n) = pretty n
  pretty (TgInternal v) = text v
