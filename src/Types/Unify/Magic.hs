{-# LANGUAGE ConstraintKinds, FlexibleContexts #-}
module Types.Unify.Magic (magicClass) where

import Control.Monad.Infer
import Control.Lens

import Syntax.Implicits
import Syntax.Builtin
import Syntax.Types
import Syntax.Var
import Syntax

import Data.Spanned

type Solver m = SomeReason -> ImplicitScope ClassInfo Typed -> Type Typed -> m (Maybe (Wrapper Typed))
type MonadSolve m = (MonadNamey m, MonadWriter [Constraint Typed] m, MonadChronicles TypeError m)

magicClass :: MonadSolve m => Var Typed -> Maybe (Solver m)
magicClass v
  | v == tyKStrName = Just (solveKnownLit knownStrName knownStrTy knownStrTy' tyKStr tyString)
  | v == tyKIntName = Just (solveKnownLit knownIntName knownIntTy knownIntTy' tyKInt tyInt)
  | v == rowConsName = Just solveRowCons
  | v == tyEqName = Just solveEq
  | otherwise = Nothing

solveEq :: MonadSolve m => Solver m
solveEq blame classes ty@(TyApps _ [a, b]) = do
  var <- genName
  tell [ ConUnify blame classes var a b ]
  let refl = ExprWrapper (Cast (AppCo (AppCo (ReflCo tyEq) (MvCo var)) (MvCo var)))
                (ExprWrapper (TypeApp a) (VarRef rEFLName (span, rEFLTy)) (span, rEFLTy' a))
                (span, ty)
      span = annotation blame
  pure (Just (ExprApp refl))
solveEq _ _ _ = undefined

solveKnownLit :: MonadSolve m
              => Var Resolved -> Type Typed -> (Type Typed -> Type Typed) -> Type Typed -> Type Typed
              -> Solver m
solveKnownLit name ty ty' constraint return blame _ (TyApp _ str) =
  case str of
    TyLit l -> pure $ pure (solution l)
    _ -> pure Nothing
  where
    solution :: Lit -> Wrapper Typed
    solution t = ExprApp $
      App (ExprWrapper (TypeApp (TyLit t))
            (VarRef name (span, ty))
            (span, ty' (TyLit t)))
          (Literal t (span, return))
          (span, TyApp constraint (TyLit t))
    span = annotation blame
solveKnownLit _ _ _ _ _ _ _ _ = error "kind error in solveKnownString"

solveRowCons :: MonadSolve m => Solver m
solveRowCons blame classes ty =
  case appsView ty of
    [ _, record@TyVar{}, TyLit (LiStr key), tau, new ] | isRows new -> do
      x <- genName
      tell [ ConUnify blame classes x (TyRows record [ (key, tau )]) new ]
      pure (pure (solution record tau key new))
    [ _, record, TyLit (LiStr key), tau, new ] | isRows record -> do
      x <- genName
      let (innermost, ks) = getRows record
      case innermost of
        Just t -> tell [ ConUnify blame classes x (TyRows t ((key, tau):(ks `without` key)) ) new ]
        _      -> tell [ ConUnify blame classes x (TyExactRows ((key, tau):(ks `without` key)) ) new ]
      pure (pure (solution record tau key new))
    _ -> pure Nothing
  where
    solution record tau key new =
      let solution =
            App (ExprWrapper (TypeApp new)
                  (ExprWrapper (TypeApp tau)
                    (ExprWrapper (TypeApp record)
                      (ExprWrapper (TypeApp keyt)
                        (VarRef rOWCONSName (span, rowConsTy))
                        (span, rowConsTy' keyt))
                      (span, rowConsTy'' keyt record))
                    (span, rowConsTy''' keyt record tau))
                  (span, rowConsTy'''' keyt record tau new))
                (Literal (LiStr key) (span, tyString))
                (span, ty)
          keyt = TyLit (LiStr key)
       in ExprApp solution
    span = annotation blame
    xs `without` b = filter ((/= b) . fst) xs

    getRows (TyExactRows rs) = (Nothing, rs)
    getRows (TyRows t rs) = getRows t & _2 %~ (rs ++)
    getRows t = (Just t, [])

isRows :: Type p -> Bool
isRows TyExactRows{} = True
isRows TyRows{} = True
isRows _ = False
