{-# LANGUAGE
  OverloadedStrings
, LambdaCase
, FlexibleContexts
, DeriveFunctor
, TemplateHaskell #-}

-- | Track variables in the current scope while resolving 'Syntax'. This
-- also tracks ambiguous definitions and modules.
module Syntax.Resolve.Scope
  ( VarName
  , EnvSlot(..)
  , ModuleEnvironment(..)
  , Environment(..), envValues, envTypes, envModules, envClasses
  , Context(..), env, typeVars
  , emptyContext
  , tagVar
  , withValues, extendValues, extendTyvars
  , prefixEnv
  ) where

import qualified Data.Map as Map
import qualified Data.Text as T
import Data.Function
import Data.List

import Control.Monad.Reader
import Control.Monad.Namey
import Control.Lens hiding (Context)

import Syntax.Var
import Syntax

-- | The name of your variables
type VarName = T.Text

-- | A variable in the current scope
data EnvSlot a
  = EKnown a       -- ^ Can be resolved to a specific definition site
  | EAmbiguous [a] -- ^ Can be resolved to 2 or more definition sites.
  deriving (Eq, Ord, Show, Functor)

data ModuleEnvironment
  = EnvModule Environment
  | EnvFunctor VarName (ModuleType Typed) (ModuleType Typed)
  deriving (Show)

-- | The current environment of a module
data Environment =
  Environment
  { -- | Values visible in this module
    _envValues :: Map.Map VarName (EnvSlot (Var Resolved))
    -- | Types visible in this module
  , _envTypes :: Map.Map VarName (Var Resolved)
    -- | Modules visible in this module
  , _envModules :: Map.Map VarName (Var Resolved, ModuleEnvironment)
    -- | Classes visible in this module
  , _envClasses :: Map.Map VarName (Var Resolved)
  }
  deriving (Show)

instance Semigroup Environment where
  Environment v t m c <> Environment v' t' m' c' = Environment (v <> v') (t <> t') (m <> m') (c <> c')

instance Monoid Environment where
  mempty = Environment mempty mempty mempty mempty

-- | The current context to resolve in
data Context =
  Context
  { _env :: Environment
  , _typeVars :: Map.Map VarName (EnvSlot (Var Resolved))
  }
  deriving (Show)

makeLenses ''Context
makeLenses ''Environment

-- | An empty resolution context
emptyContext :: Context
emptyContext = Context mempty mempty

-- | Convert a parsed variable into a resolved one. This requires that
-- the variable is unqualified.
tagVar :: MonadNamey m => Var Parsed -> m (Var Resolved)
tagVar (Name n) = TgName . Ident n <$> gen

-- | Insert one or more variables into a map. If multiple variables with
-- the same name are defined, this will be considered as ambiguous.
insertN :: Map.Map VarName (EnvSlot a)
        -> [(Var Parsed, a)]
        -> Map.Map VarName (EnvSlot a)
insertN scope = foldr (\case
                          [(Name v, v')] -> Map.insert v (EKnown v')
                          vs@((Name v,_):_) -> Map.insert v (EAmbiguous (map snd vs))
                          _ -> undefined) scope
                . groupBy ((==) `on` fst)
                . sortOn fst

-- | Create a scope with one or more variables
withValues :: [(Var Parsed, Var Resolved)] -> Environment -> Environment
withValues vs = envValues %~ flip insertN vs

-- | Create a scope with one or more type variables and evaluate the
-- provided monad within it.
extendValues :: MonadReader Context m => [(Var Parsed, Var Resolved)] -> m a -> m a
extendValues vs = local (env %~ withValues vs)

-- | Create a scope with one or more type variables and evaluate the
-- provided monad within it.
extendTyvars :: MonadReader Context m => [(Var Parsed, Var Resolved)] -> m a -> m a
extendTyvars vs = local (typeVars %~ flip insertN vs)

gen :: MonadNamey m => m Int
gen = (\(Ident _ i) -> i) <$> genIdent

prefixEnv :: Var Resolved -> Environment -> Environment
prefixEnv var env =
  Environment
  { _envValues = fmap dot <$> _envValues env
  , _envTypes  = dot <$> _envTypes env
  , _envModules = go <$> _envModules env
  , _envClasses = dot <$> _envClasses env
  }
  where
    go (n, EnvModule e) = (dot n, EnvModule (prefixEnv var e))

    dot (TgName n) = undefined var n -- TODO:
    dot n@TgInternal{} = n
