{-# LANGUAGE FlexibleContexts
  , UndecidableInstances
  , FlexibleInstances
  , GADTs
  , ConstraintKinds
  , StandaloneDeriving
  , MultiParamTypeClasses
  , OverloadedStrings
  , ScopedTypeVariables
  , RecordWildCards
  , ViewPatterns
  , NamedFieldPuns
  #-}
module Control.Monad.Infer
  ( module M, firstName
  , Env
  , MonadInfer, Name
  , lookupTy, lookupTy', genNameFrom, genNameWith, runInfer, freeInEnv
  , difference, freshTV, refreshTV
  , instantiate
  , SomeReason(..), Reasonable, addBlame
  , becauseExp, becausePat

  -- lenses:
  , names, typeVars
  , InstLevel(..)
  )
  where

import Control.Monad.Writer.Strict as M hiding ((<>))
import Control.Monad.Chronicles as M
import Control.Monad.Reader as M
import Control.Monad.Namey as M
import Control.Lens

import qualified Data.Map.Strict as Map
import qualified Data.Sequence as Seq
import Data.These.Lens
import Data.Foldable
import Data.Spanned
import Data.Triple
import Data.Reason
import Data.Maybe
import Data.These
import Data.Text (Text)

import Syntax.Types
import Syntax.Subst
import Syntax

import Types.Error as M

type MonadInfer p m =
  ( MonadChronicles TypeError m
  , MonadReader Env m
  , MonadWriter (Seq.Seq (Constraint p)) m
  , MonadNamey m)

data InstLevel = Weak | Strong
  deriving (Eq)

lookupTy :: (MonadChronicles TypeError m, MonadReader Env m, MonadNamey m) => Var Desugared -> m (Type Typed)
lookupTy x = do
  rs <- view (names . at x)
  case rs of
    Just t -> thd3 <$> instantiate Strong Expression t
    Nothing -> confesses (NotInScope' x)

lookupTy' :: (MonadChronicles TypeError m, MonadReader Env m, MonadNamey m)
          => InstLevel -> Var Desugared
          -> m (Maybe (Expr Typed -> Expr Typed), Type Typed, Type Typed)
lookupTy' str x = do
  rs <- view (names . at x)
  case rs of
    Just t -> instantiate str Expression t
    Nothing -> confesses (NotInScope' x)

runInfer :: MonadNamey m
         => Env
         -> ReaderT Env (WriterT (Seq.Seq (Constraint p)) (ChroniclesT TypeError m)) a
         -> m (These [TypeError] (a, Seq.Seq (Constraint p)))
runInfer ct ac = over here toList <$>
  runChronicleT (runWriterT (runReaderT ac ct))

genNameFrom :: MonadNamey m => Text -> m (Var Desugared)
genNameFrom t = genNameUsing (const t)

genNameWith :: MonadNamey m => Text -> m (Var Desugared)
genNameWith t = genNameUsing (t<>)

firstName :: Ident
firstName = Ident "a" 0

instantiate :: MonadNamey m
            => InstLevel
            -> WhyInstantiate
            -> Type Typed
            -> m ( Maybe (Expr Typed -> Expr Typed)
                 , Type Typed
                 , Type Typed)
instantiate str r tp@(TyPi (Invisible v _ spec) ty) | can str spec = do
  var <- refreshTV v
  let map = Map.singleton v var

      appThisTy e = ExprWrapper (TypeApp var) e (annotation e, apply map ty)
  (k, _, t) <- instantiate str r (apply map ty)
  pure (squish appThisTy k, tp, t)

instantiate str r tp@(TyPi (Anon co) od@dm) = do
  (wrap, _, dm) <- instantiate str r dm
  let cont = fromMaybe id wrap
  var <- genName
  let ty = TyPi (Anon co) dm
      lam :: Expr Typed -> Expr Typed
      lam e | od == dm = e
      lam e
        | ann <- annotation e
        = Fun (PatParam (PType (Capture var (ann, co)) co (ann, co)))
           (cont (App e (VarRef var (ann, co)) (ann, od))) (ann, ty)

  pure (Just lam, tp, ty)

instantiate str r tp@(TyPi (Implicit co) od@dm) = do
  (wrap, _, dm) <- instantiate str r dm
  let cont = fromMaybe id wrap
  var <- genName
  let ty = TyPi (Implicit co) dm
      lam :: Expr Typed -> Expr Typed
      lam e | od == dm = e
      lam e
        | ann <- annotation e
        = Fun (EvParam (PType (Capture var (ann, co)) co (ann, co)))
            (cont (App e (VarRef var (ann, co)) (ann, od))) (ann, ty)

  pure (Just lam, tp, ty)

instantiate _ _ ty = pure (Just id, ty, ty)

can :: InstLevel -> Specificity -> Bool
can Strong x = case x of
  Req -> False
  _ -> True
can Weak Infer = True
can Weak _ = False

freshTV :: MonadNamey m => m (Type Typed)
freshTV = TyVar <$> genName

refreshTV :: MonadNamey m => Var Typed -> m (Type Typed)
refreshTV v = TyVar <$> genNameFrom nm where
  nm = case v of
    TgInternal x -> x
    TgName (Ident x _) -> x

squish :: (a -> c) -> Maybe (c -> c) -> Maybe (a -> c)
squish f = Just . maybe f (.f)

addBlame :: SomeReason -> TypeError -> TypeError
addBlame _ e@ArisingFrom{} = e
addBlame x e = ArisingFrom e x
