{-# LANGUAGE DerivingStrategies, GeneralizedNewtypeDeriving,
   FlexibleContexts, FlexibleInstances, MultiParamTypeClasses,
   UndecidableInstances #-}

{-| The compiler often needs a source of fresh variables, such as when
  performing optimisations or creating new type variables during
  inference.

  Instead of piping through some concrete generator, we use 'MonadNamey'
  as a source of fresh 'Name's, which may then be converted to other
  variables as needed.
-}
module Control.Monad.Namey
  ( NameyT, runNameyT, evalNameyT
  , Namey, runNamey, evalNamey
  , MonadNamey(..)
  , genAlnum, genName, genNameUsing
  ) where

import qualified Control.Monad.Writer.Strict as StrictW
import qualified Control.Monad.State.Strict as StrictS
import qualified Control.Monad.RWS.Strict as StrictRWS
import qualified Control.Monad.Chronicle as Chronicle
import qualified Control.Monad.Writer.Lazy as LazyW
import qualified Control.Monad.State.Lazy as LazyS
import qualified Control.Monad.RWS.Lazy as LazyRWS
import qualified Control.Monad.Reader as Reader
import Control.Monad.State.Class
import Control.Monad.IO.Class
import Control.Monad.Except
import Control.Applicative
import Control.Monad.Cont
import Control.Arrow

import qualified Data.Text as T
import Data.Functor.Identity
import Data.Fixed
import Data.Char

import Syntax.Var

-- | The namey monad transformer
--
-- This is both an instance of 'MonadState' and 'MonadNamey', allowing it
-- to be used with lenses.
newtype NameyT m a =
  NameyT (StrictS.StateT Int m a)
  deriving newtype
  ( Functor
  , Applicative
  , Monad
  , MonadTrans
  , MonadPlus
  , Alternative
  , Reader.MonadReader r
  , StrictW.MonadWriter w
  , MonadError e
  , MonadIO
  )

-- | The namey monad
type Namey = NameyT Identity

instance MonadState s m => MonadState s (NameyT m) where
  get = lift StrictS.get
  put = lift . StrictS.put

-- | A source of fresh variable names
class Monad m => MonadNamey m where
  -- | Get a fresh variable
  genIdent :: m Ident

-- | Run the namey monad transformer with some starting name, returning
-- the result of the computation and the next name to generate.
runNameyT :: Functor m => NameyT m a -> Ident -> m (a, Ident)
runNameyT (NameyT k) (Ident _ i) = second genVar <$> StrictS.runStateT k i where
  genVar x = Ident (genAlnum x) x

-- | Run the namey monad transformer with some starting name, returning
-- the result of the computation.
evalNameyT :: Monad m => NameyT m a -> Ident -> m a
evalNameyT (NameyT k) (Ident _ i) = StrictS.evalStateT k i

-- | Run the namey monad with some starting name, returning the result of
-- the computation and the next name to generate.
runNamey :: NameyT Identity a -> Ident -> (a, Ident)
runNamey (NameyT k) (Ident _ i) = second genVar $ StrictS.runState k i where
  genVar x = Ident (genAlnum x) x

-- | Run the namey monad with some starting name, returning the result of
-- the computation.
evalNamey :: NameyT Identity a -> Ident -> a
evalNamey (NameyT k) (Ident _ i) = StrictS.evalState k i

instance Monad m => MonadNamey (NameyT m) where
  genIdent = NameyT $ do
    x <- get
    put (x + 1)
    pure (Ident (genAlnum x) x)

instance MonadNamey m => MonadNamey (ContT r m) where
  genIdent = lift genIdent

instance MonadNamey m => MonadNamey (StrictS.StateT s m) where
  genIdent = lift genIdent

instance MonadNamey m => MonadNamey (LazyS.StateT s m) where
  genIdent = lift genIdent

instance (MonadNamey m, Monoid s) => MonadNamey (StrictW.WriterT s m) where
  genIdent = lift genIdent

instance (MonadNamey m, Monoid s) => MonadNamey (LazyW.WriterT s m) where
  genIdent = lift genIdent

instance MonadNamey m => MonadNamey (ExceptT e m) where
  genIdent = lift genIdent

instance MonadNamey m => MonadNamey (Reader.ReaderT e m) where
  genIdent = lift genIdent

instance (Semigroup c, MonadNamey m) => MonadNamey (Chronicle.ChronicleT c m) where
  genIdent = lift genIdent

instance (MonadNamey m, Monoid w) => MonadNamey (StrictRWS.RWST r w s m) where
  genIdent = lift genIdent

instance (MonadNamey m, Monoid w) => MonadNamey (LazyRWS.RWST r w s m) where
  genIdent = lift genIdent

-- | Generate an lowercase letter-based representation of a integer
-- identifier. This is used to generate slightly more readable variable
-- names.
genAlnum :: Int -> T.Text
genAlnum 0 = T.singleton 'a'
genAlnum n = go (fromIntegral n) T.empty (floor (logBase 26 (fromIntegral n :: Double))) where
  go :: Double -> T.Text -> Int -> T.Text
  go n out 0 = T.snoc out (chr (97 + floor n))
  go n out p =
    let m :: Int
        m = case floor (n / (26 ^ p)) of
              0 -> 1
              x -> x
     in go (n `mod'` (26 ^ p)) (T.snoc out (chr (96 + m))) (p - 1)

-- | Generate a random 'TgName'
genName :: MonadNamey m => m Name
genName = TgName <$> genIdent

-- | Generate a random 'TgName' and provide a custom name.
genNameUsing :: MonadNamey m => (T.Text -> T.Text) -> m Name
genNameUsing f = do
  Ident n i <- genIdent
  pure $ TgName (Ident (f n) i)
