{-# LANGUAGE FlexibleContexts
  , ConstraintKinds
  , OverloadedStrings
  , MultiParamTypeClasses
  , TupleSections
  , TypeFamilies
  , ScopedTypeVariables #-}

{- | The resolver is the first step after parsing. It performs several key
   actions:

    * Determines what variable every identifier is pointing to, including
      a module's variables and handling ambiguous variables.

    * Handles module definitions and @open@s.

    * Prohibit some dubious constructs, such as patterns which bind the
      same identifier multiple times.

    * Reorganise binary operators, taking precedence and associativity
      into account (the parser ignores these intentionally).
-}
module Syntax.Resolve
  ( resolveProgram
  , ResolveError(..)
  , VarKind(..)
  ) where

import Control.Lens hiding (Lazy, Context)
import Control.Monad.Chronicles
import Control.Monad.Reader
import Control.Monad.Namey

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as T
import Data.Traversable
import Data.Sequence (Seq)
import Data.Bifunctor
import Data.Foldable
import Data.Function
import Data.Functor
import Data.Reason
import Data.Triple
import Data.Maybe
import Data.These
import Data.List

import Syntax.Resolve.Scope
import Syntax.Resolve.Error
import Syntax.Subst
import Syntax

import Parser.Unicode

type MonadResolve m = ( MonadChronicles ResolveError m
                      , MonadReader Context m
                      , MonadNamey m )

-- | Resolve a program within a given 'Scope' and 'ModuleScope'
resolveProgram :: MonadNamey m
               => Environment -- ^ The scope in which to resolve this program
               -- ^ The current module scope. We return an updated
               -- version of this if we declare or extend any modules.
               -> [Toplevel Parsed] -- ^ The program to resolve
               -> m (Either [ResolveError] ([Toplevel Resolved], Environment))
               -- ^ The resolved program or a list of resolution errors
resolveProgram scope = runResolve scope
                     . flip resolveToplevel scope

-- | Run the resolver monad.
runResolve :: MonadNamey m
           => Environment -- ^ The initial state to resolve objects in
           -> ReaderT Context (ChronicleT (Seq ResolveError) m) a
           -> m (Either [ResolveError] a)
runResolve scope
  = (these (Left . toList) Right (\x _ -> Left (toList x))<$>)
  . runChronicleT . flip runReaderT (Context scope mempty)


lookupIn :: MonadResolve m
         => (Environment -> Map.Map VarName a)
         -> Var Parsed -> VarKind -> Environment
         -> m a
lookupIn g v@(Name n) k env =
  case Map.lookup n (g env) of
    Nothing -> confesses (NotInScope k v [])
    Just x -> pure x

lookupSlot :: MonadResolve m
          => Var Parsed -> EnvSlot (Var Resolved)
          -> m (Var Resolved)
lookupSlot v slot =
  case slot of
    EAmbiguous vs -> confesses (Ambiguous v vs)
    EKnown x -> pure x

lookupEx :: MonadResolve m => Var Parsed -> m (Var Resolved)
lookupEx v = view env
         >>= lookupIn (^.envValues) v (if isCtorVar v then VarCtor else VarVar)
         >>= lookupSlot v

lookupTy :: MonadResolve m => Var Parsed -> m (Var Resolved)
lookupTy v = view env
         >>= lookupIn (^.envTypes) v (if isCtorVar v then VarCtor else VarType)

lookupMod :: MonadResolve m => Var Parsed -> m (Var Resolved, ModuleEnvironment)
lookupMod v = view env >>= lookupIn (^.envModules) v VarModule

lookupTyvar :: MonadResolve m => Var Parsed -> m (Var Resolved)
lookupTyvar v@(Name n) = do
  s <- view typeVars
  case Map.lookup n s of
    Nothing -> confesses (NotInScope VarTyvar v [])
    Just x -> lookupSlot v x

-- | Resolve the whole program
resolveToplevel :: MonadResolve m
              => [Toplevel Parsed] -> Environment
              -> m ([Toplevel Resolved], Environment)
resolveToplevel [] env = pure ([], env)

resolveToplevel (LetStmt am bs:rs) env = do
  (bs', vs, ts) <- unzip3 <$> traverse reBinding bs
  doTop rs env am (withValues (concat vs)) $ extendTyvars (concat ts) $
    LetStmt am <$> traverse (uncurry (flip (<$>) . reExpr . view bindBody)) (zip bs bs')

resolveToplevel (r@(ForeignVal am v t ty a):rs) env = do
  v' <- tagVar v
  doTop rs env am (envValues %~ Map.insert (varName v) (EKnown v')) $
    ForeignVal am
      <$> lookupEx v `catchJunk` r
      <*> pure t
      <*> reType r (wrap ty)
      <*> pure a

  where wrap x = foldr (TyPi . flip (flip Invisible Nothing) Spec) x (toList (ftv x))
resolveToplevel (d@(TypeDecl am t vs cs):rs) env = do
  t'  <- tagVar t
  (vs', sc) <- resolveTele d vs
  let c = map extractCons cs
  c' <- traverse tagVar c
  doTop rs env am ((envTypes %~ Map.insert (varName t) t') . withValues (zip c c')) $
    TypeDecl am t' vs' <$> traverse (resolveCons sc) (zip cs c')

  where resolveCons _ (UnitCon ac _ a, v') = pure $ UnitCon ac v' a
        resolveCons vs (r@(ArgCon ac _ t a), v') = ArgCon ac v' <$> extendTyvars vs (reType r t) <*> pure a
        resolveCons _  (r@(GadtCon ac _ t a), v') = do
          let fvs = toList (ftv t)
          fresh <- traverse tagVar fvs
          t' <- extendTyvars (zip fvs fresh) (reType r t)
          pure (GadtCon ac v' t' a)

        extractCons (UnitCon _ v _) = v
        extractCons (ArgCon _ v _ _) = v
        extractCons (GadtCon _ v _ _) = v

resolveToplevel (Module am name mod:rs) env' = do
  (mod', mEnv) <- resolveModTerm mod
  name' <- tagVar name
  doTop rs env' am (envModules %~ Map.insert (varName name) (name', EnvModule $ prefixEnv name' mEnv)) $
    pure $ Module am name' mod'

resolveToplevel (Open am body:rs) env' = do
  (mod', mEnv) <- resolveModTerm body
  doTop rs env' am (mEnv<>) . pure $ Open am mod'

resolveToplevel (t@(Class name am ctx tvs ms ann):rs) env' = do
  name' <- tagVar name
  (tvs', tvss) <- resolveTele t tvs

  (ctx', (ms', vs')) <- extendTyvars tvss $ local (env . envTypes %~ Map.insert (varName name) name') $
      (,) <$> traverse (reType t) ctx
          <*> (unzip <$> traverse (reClassItem (map fst tvss)) ms)


  doTop rs env' am ((envTypes %~ Map.insert (varName name) name') . withValues (mconcat vs')) $ do
    ms'' <- extendTyvars tvss (sequence ms')
    pure $ Class name' am ctx' tvs' ms'' ann

  where
    reClassItem tvs' m@(MethodSig name ty an) = do
      name' <- tagVar name
      pure ( MethodSig name' <$> reType m (wrap tvs' ty) <*> pure an
           , [(name, name')] )
    reClassItem _ (DefaultMethod b an) =
      pure ( DefaultMethod <$> (fst =<< reMethod b) <*> pure an
           , [] )
    wrap tvs' x = foldr (TyPi . flip (flip Invisible Nothing) Spec) x (ftv x `Set.difference` Set.fromList tvs')

resolveToplevel (t@(Instance cls ctx head ms ann):rs) env = do
  cls' <- lookupTy cls `catchJunk` t

  let fvs = toList (foldMap ftv ctx <> ftv head)
  fvs' <- traverse tagVar fvs

  t' <- extendTyvars (zip fvs fvs') $ do
    ctx' <- traverse (reType t) ctx
    head' <- reType t head

    (ms', vs) <- unzip <$> traverse reMethod ms
    ms'' <- extendValues (concat vs) (sequence ms')

    pure (Instance cls' ctx' head' ms'' ann)

  first (t':) <$> resolveToplevel rs env

resolveModTerm :: MonadResolve m
               => ModuleTerm Parsed
               -> m (ModuleTerm Resolved, Environment)
resolveModTerm (ModStruct b) = first ModStruct <$> resolveToplevel b mempty
resolveModTerm (ModName n) = do
  mod <- lookupMod n
  case mod of
    (n', EnvModule e) -> pure (ModName n', e)

resolveTele :: (MonadResolve m, Reasonable f p)
            => f p -> [TyConArg Parsed] -> m ([TyConArg Resolved], [(Var Parsed, Var Resolved)])
resolveTele r (TyVarArg v:as) = do
  v' <- tagVar v
  (as, vs) <- resolveTele r as
  pure (TyVarArg v':as, (v, v'):vs)
resolveTele r (TyAnnArg v k:as) = do
  v' <- tagVar v
  ((as, vs), k) <-
    (,) <$> resolveTele r as <*> reType r k
  pure (TyAnnArg v' k:as, (v, v'):vs)
resolveTele _ [] = pure ([], [])

reExpr :: MonadResolve m => Expr Parsed -> m (Expr Resolved)
reExpr r@(VarRef v a) = flip VarRef a <$> (lookupEx v `catchJunk` r)

reExpr (Let bs c a) = do
  (bs', vs, ts) <- unzip3 <$> traverse reBinding bs
  extendTyvars (concat ts) . extendValues (concat vs) $
    Let <$> traverse (uncurry (flip (<$>) . reExpr . view bindBody)) (zip bs bs')
        <*> reExpr c
        <*> pure a
reExpr (If c t b a) = If <$> reExpr c <*> reExpr t <*> reExpr b <*> pure a
reExpr (App f p a) = App <$> reExpr f <*> reExpr p <*> pure a
reExpr (Fun p e a) = do
  let reWholePattern' (PatParam p) = do
        (p', vs, ts) <- reWholePattern p
        pure (PatParam p', vs, ts)
      reWholePattern' _ = error "EvParam resolve"
  (p', vs, ts) <- reWholePattern' p
  extendTyvars ts . extendValues vs $ Fun p' <$> reExpr e <*> pure a

reExpr r@(Begin [] a) = dictates (wrapError r EmptyBegin) $> junkExpr a
reExpr (Begin es a) = Begin <$> traverse reExpr es <*> pure a

reExpr (Literal l a) = pure (Literal l a)

reExpr (Match e ps a) = do
  e' <- reExpr e
  ps' <- traverse reArm ps
  pure (Match e' ps' a)

reExpr r@(Function [] a) = dictates (ArisingFrom EmptyMatch (BecauseOf r)) $> junkExpr a
reExpr (Function ps a) = flip Function a <$> traverse reArm ps

reExpr (BinOp l o r a) = BinOp <$> reExpr l <*> reExpr o <*> reExpr r <*> pure a
reExpr (Hole v a) = Hole <$> tagVar v <*> pure a
reExpr r@(Ascription e t a) = Ascription
                          <$> reExpr e
                          <*> reType r t
                          <*> pure a
reExpr e@(Record fs a) = do
  let ls = map (view fName) fs
      dupes = mapMaybe (listToMaybe . tail) . group . sort $ ls
  traverse_ (dictates . NonLinearRecord e) dupes
  Record <$> traverse reField fs <*> pure a
reExpr ex@(RecordExt e fs a) = do
  let ls = map (view fName) fs
      dupes = mapMaybe (listToMaybe . tail) . group . sort $ ls
  traverse_ (dictates . NonLinearRecord ex) dupes
  RecordExt <$> reExpr e <*> traverse reField fs <*> pure a

reExpr (Access e t a) = Access <$> reExpr e <*> pure t <*> pure a
reExpr (LeftSection o r a) = LeftSection <$> reExpr o <*> reExpr r <*> pure a
reExpr (RightSection l o a) = RightSection <$> reExpr l <*> reExpr o <*> pure a
reExpr (BothSection o a) = BothSection <$> reExpr o <*> pure a
reExpr (AccessSection t a) = pure (AccessSection t a)
reExpr (Parens e a) = flip Parens a <$> reExpr e

reExpr (Tuple es a) = Tuple <$> traverse reExpr es <*> pure a
reExpr (ListExp es a) = ListExp <$> traverse reExpr es <*> pure a
reExpr (TupleSection es a) = TupleSection <$> traverse (traverse reExpr) es <*> pure a

reExpr r@(OpenIn m e a) = do
  res <- recover Nothing . retcons (wrapError r) $ Just <$> resolveModTerm m
  case res of
    Just (m', mEnv) -> local (env %~ (mEnv<>)) (OpenIn m' <$> reExpr e <*> pure a)
    Nothing -> pure (VarRef junkVar a)

reExpr (Lazy e a) = Lazy <$> reExpr e <*> pure a
reExpr (Vta e t a) = Vta <$> reExpr e <*> reType e t <*> pure a

reExpr (ListComp e qs a) =
  let go (CompGuard e:qs) acc = do
        e <- reExpr e
        go qs (CompGuard e:acc)
      go (CompGen b e an:qs) acc = do
        e <- reExpr e
        (b, es, ts) <- reWholePattern b
        extendTyvars ts . extendValues es $
          go qs (CompGen b e an:acc)
      go (CompLet bs an:qs) acc =do
        (bs', vs, ts) <- unzip3 <$> traverse reBinding bs
        extendTyvars (concat ts) . extendValues (concat vs) $ do
          bs <- traverse (uncurry (flip (<$>) . reExpr . view bindBody)) (zip bs bs')
          go qs (CompLet bs an:acc)
      go [] acc = ListComp <$> reExpr e <*> pure (reverse acc) <*> pure a
  in go qs []

reExpr ExprWrapper{} = error "resolve cast"

reArm :: MonadResolve m
      => Arm Parsed -> m (Arm Resolved)
reArm (Arm p g b) = do
  (p', vs, ts) <- reWholePattern p
  extendTyvars ts . extendValues vs $
    Arm p' <$> traverse reExpr g <*> reExpr b


reType :: (MonadResolve m, Reasonable a p)
       => a p -> Type Parsed -> m (Type Resolved)
reType r (TyCon v) = TyCon <$> (lookupTy v `catchJunk` r)
reType r (TyVar v) = TyVar <$> (lookupTyvar v `catchJunk` r)
reType r (TyPromotedCon v) = TyPromotedCon <$> (lookupEx v `catchJunk` r)
reType _ v@TySkol{} = error ("impossible! resolving skol " ++ show v)
reType _ v@TyWithConstraints{} = error ("impossible! resolving withcons " ++ show v)
reType r (TyPi (Invisible v k req) ty) = do
  v' <- tagVar v
  ty' <- extendTyvars [(v, v')] $ reType r ty
  k <- traverse (reType r) k
  pure (TyPi (Invisible v' k req) ty')
reType r (TyPi (Anon f) x) = TyPi . Anon <$> reType r f <*> reType r x
reType r (TyPi (Implicit f) x) = TyPi . Implicit <$> reType r f <*> reType r x
reType r (TyApp f x) = TyApp <$> reType r f <*> reType r x
reType r (TyRows t f) = TyRows <$> reType r t
                               <*> traverse (\(a, b) -> (a,) <$> reType r b) f
reType r (TyExactRows f) = TyExactRows <$> traverse (\(a, b) -> (a,) <$> reType r b) f
reType r (TyTuple ta tb) = TyTuple <$> reType r ta <*> reType r tb
reType _ (TyWildcard _) = pure (TyWildcard Nothing)
reType r (TyParens t) = TyParens <$> reType r t
reType r (TyOperator tl o tr) = TyOperator <$> reType r tl <*> (lookupTy o `catchJunk` r) <*> reType r tr
reType _ TyType = pure TyType

reWholePattern :: forall m. MonadResolve m
               => Pattern Parsed
               -> m ( Pattern Resolved
                    , [(Var Parsed, Var Resolved)]
                    , [(Var Parsed, Var Resolved)])
reWholePattern p = do
  -- Resolves a pattern and ensures it is linear
  (p', vs, ts) <- rePattern p
  checkLinear vs
  checkLinear ts
  pure (p', map lim vs, map lim ts)

 where checkLinear :: [(Var Parsed, Var Resolved, Pattern Resolved)] -> m ()
       checkLinear = traverse_ (\vs@((_,v, _):_) -> dictates . wrapError p $ NonLinearPattern v (map thd3 vs))
                   . filter ((>1) . length)
                   . groupBy ((==) `on` fst3)
                   . sortOn fst3
       lim (a, b, _) = (a, b)

rePattern :: MonadResolve m
          => Pattern Parsed
          -> m ( Pattern Resolved
               , [(Var Parsed, Var Resolved, Pattern Resolved)]
               , [(Var Parsed, Var Resolved, Pattern Resolved )])
rePattern (Wildcard a) = pure (Wildcard a, [], [])
rePattern (Capture v a) = do
  v' <- tagVar v
  let p = Capture v' a
  pure (p, [(v, v', p)], [])
rePattern (PAs p v a) = do
  v' <- tagVar v
  (p', vs, ts) <- rePattern p
  let as = PAs p' v' a
  pure (as, (v, v', as):vs, ts)
rePattern r@(Destructure v Nothing a) = do
  v' <- lookupEx v `catchJunk` r
  pure (Destructure v' Nothing a, [], [])
rePattern r@(Destructure v p a) = do
  v' <- lookupEx v `catchJunk` r
  (p', vs, ts) <- case p of
    Nothing -> pure (Nothing, [], [])
    Just pat -> do
      (p', vs, ts) <- rePattern pat
      pure (Just p', vs, ts)
  pure (Destructure v' p' a, vs, ts)
rePattern r@(PType p t a) = do
  (p', vs, ts) <- rePattern p
  let fvs = toList (ftv t)
  fresh <- for fvs $ \x -> lookupTyvar x `absolving` tagVar x
  t' <- extendTyvars (zip fvs fresh) (reType r t)
  let r' = PType p' t' a
  pure (r', vs, zip3 fvs fresh (repeat r') ++ ts)
rePattern (PRecord f a) = do
  (f', vss, tss) <- unzip3 <$> traverse (\(n, p) -> do
                                       (p', vs, ts) <- rePattern p
                                       pure ((n, p'), vs, ts))
                              f
  pure (PRecord f' a, concat vss, concat tss)
rePattern (PTuple ps a) = do
  (ps', vss, tss) <- unzip3 <$> traverse rePattern ps
  pure (PTuple ps' a, concat vss, concat tss)
rePattern (PList ps a) = do
  (ps', vss, tss) <- unzip3 <$> traverse rePattern ps
  pure (PList ps' a, concat vss, concat tss)
rePattern (PLiteral l a) = pure (PLiteral l a, [], [])
rePattern PWrapper{} = error "Impossible PWrapper"
rePattern PSkolem{} = error "Impossible PSkolem"

reBinding :: MonadResolve m
          => Binding Parsed
          -> m ( Expr Resolved -> Binding Resolved
               , [(Var Parsed, Var Resolved)]
               , [(Var Parsed, Var Resolved)] )
reBinding (Binding v _ c a) = do
  v' <- tagVar v
  pure ( \e' -> Binding v' e' c a, [(v, v')], [])
reBinding (Matching p _ a) = do
  (p', vs, ts) <- reWholePattern p
  pure ( \e' -> Matching p' e' a, vs, ts)
reBinding TypedMatching{} = error "reBinding TypedMatching{}"

reMethod :: MonadResolve m
         => Binding Parsed
         -> m (m (Binding Resolved), [(Var Parsed, Var Resolved)])
reMethod b@(Binding var bod c an) = do
  var' <- retcons (wrapError b) $ lookupEx var
  pure ( (\bod' -> Binding var' bod' c an) <$> reExpr bod
       , [(var, var')] )
reMethod b@(Matching (Capture var _) bod an) = do
  var' <- retcons (wrapError b) $ lookupEx var
  pure ( (\bod' -> Binding var' bod' True an) <$> reExpr bod
       , [(var, var')] )
reMethod b@Matching{} =
  confesses (ArisingFrom IllegalMethod (BecauseOf b))
reMethod TypedMatching{} = error "reBinding TypedMatching{}"

junkVar :: Var Resolved
junkVar = TgInternal "<missing>"

junkExpr :: Ann Resolved -> Expr Resolved
junkExpr = VarRef junkVar

wrapError :: Reasonable e p => e p -> ResolveError -> ResolveError
wrapError _  e@(ArisingFrom _ _) = e
wrapError r e = ArisingFrom e (BecauseOf r)

catchJunk :: (MonadResolve m, Reasonable e p)
          => m (Var Resolved) -> e p -> m (Var Resolved)
catchJunk m r = recover junkVar (retcons (wrapError r) m)

reField :: MonadResolve m => Field Parsed -> m (Field Resolved)
reField (Field n e s) = Field n <$> reExpr e <*> pure s

isCtorVar :: Var Parsed -> Bool
isCtorVar (Name t) = T.length t > 0 && classify (T.head t) == Upper

varName :: Var Parsed -> VarName
varName (Name n) = n

-- | Resolve the remaining top level functions with some expression which
-- extends the scope.
doTop :: MonadResolve m
                 => [Toplevel Parsed] -> Environment -> TopAccess
                 -> (Environment -> Environment)
                 -> m (Toplevel Resolved)
                 -> m ([Toplevel Resolved], Environment)
doTop xs e am ext x = do
  let ext' = case am of
               Public -> ext
               Private -> id
  local (env %~ ext) $ do
    x' <- x
    first (x':) <$> resolveToplevel xs (ext' e)
