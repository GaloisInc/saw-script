{- |
Module      : SAWScript.MGU
Description : SAW-Script type checking.
License     : BSD3
Maintainer  : diatchki
Stability   : provisional
-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TupleSections #-}

module SAWScript.MGU
       ( checkDecl
       , checkDeclGroup
       ) where

import SAWScript.AST
import SAWScript.Position (Pos(..), Positioned(..))

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative
#endif

import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Identity
import Data.Map (Map)
import qualified Data.Map as M
import qualified Data.Set as S

-- Ignoring source locations {{{

-- | Remove all location information from the top of a type. Use this
-- before checking for a particular canonical type former.
unlocated :: Type -> Type
unlocated (LType _ t) = unlocated t
unlocated t = t

-- }}}

-- Subst {{{

newtype Subst = Subst { unSubst :: M.Map TypeIndex Type } deriving (Show)

(@@) :: Subst -> Subst -> Subst
s2@(Subst m2) @@ (Subst m1) = Subst $ m1' `M.union` m2
  where
  m1' = fmap (appSubst s2) m1

emptySubst :: Subst
emptySubst = Subst M.empty

singletonSubst :: TypeIndex -> Type -> Subst
singletonSubst tv t = Subst $ M.singleton tv t

listSubst :: [(TypeIndex, Type)] -> Subst
listSubst = Subst . M.fromList

-- }}}

-- Most General Unifier {{{

failMGU :: String -> Either String a
failMGU = Left

assert :: Bool -> String -> Either String ()
assert b msg = unless b $ failMGU msg

mgu :: LName -> Type -> Type -> Either String Subst
mgu m (LType _ t) t2 = mgu m t t2
mgu m t1 (LType _ t) = mgu m t1 t
mgu m (TyUnifyVar i) t2 = bindVar m i t2
mgu m t1 (TyUnifyVar i) = bindVar m i t1
mgu m r1@(TyRecord ts1) r2@(TyRecord ts2) = do
  assert (M.keys ts1 == M.keys ts2) $
    "mismatched record fields: " ++ pShow r1 ++ " and " ++ pShow r2
  mgus m (M.elems ts1) (M.elems ts2)
mgu m (TyCon tc1 ts1) (TyCon tc2 ts2) = do
  assert (tc1 == tc2) $
    "mismatched type constructors: " ++ pShow tc1 ++ " and " ++ pShow tc2
  mgus m ts1 ts2
mgu _ (TySkolemVar a i) (TySkolemVar b j)
  | (a, i) == (b, j) = return emptySubst
mgu _ (TyVar a) (TyVar b)
  | a == b = return emptySubst
mgu m t1 t2 = failMGU $ "type mismatch: " ++ pShow t1 ++ " and " ++ pShow t2 ++ " at " ++ show m

mgus :: LName -> [Type] -> [Type] -> Either String Subst
mgus _ [] [] = return emptySubst
mgus m (t1:ts1) (t2:ts2) = do
  s <- mgu m t1 t2
  s' <- mgus m (map (appSubst s) ts1) (map (appSubst s) ts2)
  return (s' @@ s)
mgus m _ _ = failMGU $ "type mismatch in constructor arity at" ++ show m

bindVar :: LName -> TypeIndex -> Type -> Either String Subst
bindVar m i t
  | t == TyUnifyVar i        = return emptySubst
  | i `S.member` unifyVars t = failMGU ("occurs check failMGUs " ++ " at " ++ show m) -- FIXME: error message
  | otherwise                = return (singletonSubst i t)

-- }}}

-- UnifyVars {{{

class UnifyVars t where
  unifyVars :: t -> S.Set TypeIndex

instance (Ord k, UnifyVars a) => UnifyVars (M.Map k a) where
  unifyVars = unifyVars . M.elems

instance (UnifyVars a) => UnifyVars [a] where
  unifyVars = S.unions . map unifyVars

instance UnifyVars Type where
  unifyVars t = case t of
    TyCon _ ts      -> unifyVars ts
    TyRecord tm     -> unifyVars tm
    TyVar _         -> S.empty
    TyUnifyVar i    -> S.singleton i
    TySkolemVar _ _ -> S.empty
    LType _ t'      -> unifyVars t'

instance UnifyVars Schema where
  unifyVars (Forall _ t) = unifyVars t

-- }}}

-- NamedVars {{{

class NamedVars t where
  namedVars :: t -> S.Set Name

instance (Ord k, NamedVars a) => NamedVars (M.Map k a) where
  namedVars = namedVars . M.elems

instance (NamedVars a) => NamedVars [a] where
  namedVars = S.unions . map namedVars

instance NamedVars Type where
  namedVars t = case t of
    TyCon _ ts      -> namedVars ts
    TyRecord tm     -> namedVars tm
    TyVar n         -> S.singleton n
    TyUnifyVar _    -> S.empty
    TySkolemVar _ _ -> S.empty
    LType _ t'      -> namedVars t'

instance NamedVars Schema where
  namedVars (Forall ns t) = namedVars t S.\\ S.fromList ns

-- }}}

-- TI Monad {{{

newtype TI a = TI { unTI :: ReaderT RO (StateT RW Identity) a }
                        deriving (Functor,Applicative,Monad,MonadReader RO)

data RO = RO
  { typeEnv :: M.Map (Located Name) Schema
  , typedefEnv :: M.Map Name Type
  , currentExprPos :: Pos
  }

data RW = RW
  { nameGen :: TypeIndex
  , subst   :: Subst
  , errors  :: [(Pos, String)]
  }

emptyRW :: RW
emptyRW = RW 0 emptySubst []

newTypeIndex :: TI TypeIndex
newTypeIndex = do
  rw <- TI get
  TI $ put $ rw { nameGen = nameGen rw + 1 }
  return $ nameGen rw

newType :: TI Type
newType = TyUnifyVar <$> newTypeIndex

withExprPos :: Pos -> TI a -> TI a
withExprPos p = local (\e -> e { currentExprPos = p })

newTypePattern :: Pattern -> TI (Type, Pattern)
newTypePattern pat =
  case pat of
    PWild mt  -> do t <- maybe newType return mt
                    return (t, PWild (Just t))
    PVar x mt -> do t <- maybe newType return mt
                    return (t, PVar x (Just t))
    PTuple ps -> do (ts, ps') <- unzip <$> mapM newTypePattern ps
                    return (tTuple ts, PTuple ps')
    LPattern pos pat' -> withExprPos pos (newTypePattern pat')

appSubstM :: AppSubst t => t -> TI t
appSubstM t = do
  s <- TI $ gets subst
  return $ appSubst s t

recordError :: String -> TI ()
recordError err = do pos <- currentExprPos <$> ask
                     TI $ modify $ \rw ->
                       rw { errors = (pos, err) : errors rw }

unify :: LName -> Type -> Type -> TI ()
unify m t1 t2 = do
  t1' <- appSubstM =<< instantiateM t1
  t2' <- appSubstM =<< instantiateM t2
  case mgu m t1' t2' of
    Right s -> TI $ modify $ \rw -> rw { subst = s @@ subst rw }
    Left e -> recordError $ unlines
                [ "type mismatch: " ++ pShow t1' ++ " and " ++ pShow t2'
                , " at " ++ show m
                , e
                ]

bindSchema :: Located Name -> Schema -> TI a -> TI a
bindSchema n s m = TI $ local (\ro -> ro { typeEnv = M.insert n s $ typeEnv ro })
  $ unTI m

bindSchemas :: [(Located Name, Schema)] -> TI a -> TI a
bindSchemas bs m = foldr (uncurry bindSchema) m bs

bindDecl :: Decl -> TI a -> TI a
bindDecl (Decl _ _ Nothing _) m = m
bindDecl (Decl _ p (Just s) _) m = bindPatternSchema p s m

bindDeclGroup :: DeclGroup -> TI a -> TI a
bindDeclGroup (NonRecursive d) m = bindDecl d m
bindDeclGroup (Recursive ds) m = foldr bindDecl m ds

bindPattern :: Pattern -> TI a -> TI a
bindPattern pat = bindSchemas bs
  where bs = [ (x, tMono t) | (x, Just t) <- patternBindings pat ]

patternBindings :: Pattern -> [(Located Name, Maybe Type)]
patternBindings pat =
  case pat of
    PWild _mt -> []
    PVar x mt -> [(x, mt)]
    PTuple ps -> concatMap patternBindings ps
    LPattern _ pat' -> patternBindings pat'

bindPatternSchema :: Pattern -> Schema -> TI a -> TI a
bindPatternSchema pat s@(Forall vs t) m =
  case pat of
    PWild _ -> m
    PVar n _ -> bindSchema n s m
    PTuple ps ->
      case unlocated t of
        TyCon (TupleCon _) ts -> foldr ($) m
          [ bindPatternSchema p (Forall vs t') | (p, t') <- zip ps ts ]
        _ -> m
    LPattern pos pat' -> withExprPos pos (bindPatternSchema pat' s m)

bindTypedef :: LName -> Type -> TI a -> TI a
bindTypedef n t m =
  TI $ local (\ro -> ro { typedefEnv = M.insert (getVal n) t $ typedefEnv ro })
  $ unTI m

-- FIXME: This function may miss type variables that occur in the type
-- of a binding that has been shadowed by another value with the same
-- name. This could potentially cause a run-time type error if the
-- type of a local function gets generalized too much. We can probably
-- wait to fix it until someone finds a sawscript program that breaks.
unifyVarsInEnv :: TI (S.Set TypeIndex)
unifyVarsInEnv = do
  env <- TI $ asks typeEnv
  let ss = M.elems env
  ss' <- mapM appSubstM ss
  return $ unifyVars ss'

namedVarsInEnv :: TI (S.Set Name)
namedVarsInEnv = do
  env <- TI $ asks typeEnv
  let ss = M.elems env
  ss' <- mapM appSubstM ss
  return $ namedVars ss'

-- }}}

-- AppSubst {{{

class AppSubst t where
  appSubst :: Subst -> t -> t

instance (AppSubst t) => AppSubst [t] where
  appSubst s = map $ appSubst s

instance (AppSubst t) => AppSubst (Maybe t) where
  appSubst s = fmap $ appSubst s

instance AppSubst Type where
  appSubst s t = case t of
    TyCon tc ts     -> TyCon tc (appSubst s ts)
    TyRecord fs     -> TyRecord (appSubst s fs)
    TyVar _         -> t
    TyUnifyVar i    -> case M.lookup i (unSubst s) of
                         Just t' -> t'
                         Nothing -> t
    TySkolemVar _ _ -> t
    LType pos t'    -> LType pos (appSubst s t')

instance AppSubst Schema where
  appSubst s (Forall ns t) = Forall ns (appSubst s t)

instance AppSubst Expr where
  appSubst s expr = case expr of
    TSig e t           -> TSig (appSubst s e) (appSubst s t)
    Bool _             -> expr
    String _           -> expr
    Int _              -> expr
    Code _             -> expr
    CType _            -> expr
    Array es           -> Array (appSubst s es)
    Block bs           -> Block (appSubst s bs)
    Tuple es           -> Tuple (appSubst s es)
    Record fs          -> Record (appSubst s fs)
    Index ar ix        -> Index (appSubst s ar) (appSubst s ix)
    Lookup rec fld     -> Lookup (appSubst s rec) fld
    TLookup tpl idx    -> TLookup (appSubst s tpl) idx
    Var _              -> expr
    Function pat body  -> Function (appSubst s pat) (appSubst s body)
    Application f v    -> Application (appSubst s f) (appSubst s v)
    Let dg e           -> Let (appSubst s dg) (appSubst s e)
    IfThenElse e e2 e3 -> IfThenElse (appSubst s e) (appSubst s e2) (appSubst s e3)
    LExpr p e          -> LExpr p (appSubst s e)

instance AppSubst Pattern where
  appSubst s pat = case pat of
    PWild mt  -> PWild (appSubst s mt)
    PVar x mt -> PVar x (appSubst s mt)
    PTuple ps -> PTuple (appSubst s ps)
    LPattern _ pat' -> appSubst s pat'

instance (Ord k, AppSubst a) => AppSubst (M.Map k a) where
  appSubst s = fmap (appSubst s)

instance AppSubst Stmt where
  appSubst s bst = case bst of
    StmtBind pos pat ctx e   -> StmtBind pos (appSubst s pat) (appSubst s ctx) (appSubst s e)
    StmtLet pos dg           -> StmtLet pos (appSubst s dg)
    StmtCode pos str         -> StmtCode pos str
    StmtImport pos imp       -> StmtImport pos imp
    StmtTypedef pos name ty  -> StmtTypedef pos name (appSubst s ty)

instance AppSubst DeclGroup where
  appSubst s (Recursive ds) = Recursive (appSubst s ds)
  appSubst s (NonRecursive d) = NonRecursive (appSubst s d)

instance AppSubst Decl where
  appSubst s (Decl pos p mt e) = Decl pos (appSubst s p) (appSubst s mt) (appSubst s e)

-- }}}

-- Instantiate {{{

class Instantiate t where
  instantiate :: [(Name, Type)] -> t -> t

instance (Instantiate a) => Instantiate (Maybe a) where
  instantiate nts = fmap (instantiate nts)

instance (Instantiate a) => Instantiate [a] where
  instantiate nts = map (instantiate nts)

instance Instantiate Type where
  instantiate nts ty = case ty of
    TyCon tc ts     -> TyCon tc (instantiate nts ts)
    TyRecord fs     -> TyRecord (fmap (instantiate nts) fs)
    TyVar n         -> maybe ty id (lookup n nts)
    TyUnifyVar _    -> ty
    TySkolemVar _ _ -> ty
    LType pos ty'   -> LType pos (instantiate nts ty')

instantiateM :: Instantiate t => t -> TI t
instantiateM t = do
  s <- TI $ asks typedefEnv
  return $ instantiate (M.assocs s) t

-- }}}

-- Type Inference {{{

type OutExpr = Expr
type OutStmt = Stmt

inferE :: (LName, Expr) -> TI (OutExpr,Type)
inferE (ln, expr) = case expr of
  Bool b    -> return (Bool b, tBool)
  String s  -> return (String s, tString)
  Int i     -> return (Int i, tInt)
  Code s    -> return (Code s, tTerm)
  CType s   -> return (CType s, tType)

  Array [] ->
    do a <- newType
       return (Array [], tArray a)

  Array (e:es) ->
    do (e',t) <- inferE (ln, e)
       es' <- mapM (flip (checkE ln) t) es
       return (Array (e':es'), tArray t)

  Block bs ->
    do ctx <- newType
       (bs',t') <- inferStmts ln ctx bs
       return (Block bs', tBlock ctx t')

  Tuple es ->
    do (es',ts) <- unzip `fmap` mapM (inferE . (ln,)) es
       return (Tuple es', tTuple ts)

  Record fs ->
    do (nes',nts) <- unzip `fmap` mapM (inferField ln) (M.toList fs)
       return (Record (M.fromList nes'), TyRecord $ M.fromList nts)

  Index ar ix ->
    do (ar',at) <- inferE (ln,ar)
       ix'      <- checkE ln ix tInt
       t        <- newType
       unify ln (tArray t) at
       return (Index ar' ix', t)

  Lookup e n ->
    do (e1,t) <- inferE (ln, e)
       t1 <- appSubstM =<< instantiateM t
       elTy <- case unlocated t1 of
                 TyRecord fs
                    | Just ty <- M.lookup n fs -> return ty
                    | otherwise ->
                          do recordError $ unlines
                                [ "Selecting a missing field."
                                , "Field name: " ++ n
                                ]
                             newType
                 _ -> do recordError $ unlines
                            [ "Record lookup on non-record argument."
                            , "Field name: " ++ n
                            ]
                         newType
       return (Lookup e1 n, elTy)

  TLookup e i ->
    do (e1,t) <- inferE (ln,e)
       t1 <- appSubstM =<< instantiateM t
       elTy <- case unlocated t1 of
                 TyCon (TupleCon n) tys
                   | i < n -> return (tys !! fromIntegral i)
                   | otherwise ->
                          do recordError $ unlines
                                [ "Tuple index out of bounds."
                                , "Given index " ++ show i ++
                                  " is too large for tuple size of " ++
                                  show n
                                ]
                             newType
                 _ -> do recordError $ unlines
                            [ "Tuple lookup on non-tuple argument."
                            , "Given index " ++ show i
                            ]
                         newType
       return (TLookup e1 i, elTy)

  Var x ->
    do env <- TI $ asks typeEnv
       case M.lookup x env of
         Nothing -> do
           recordError $ "unbound variable: " ++ show x
           t <- newType
           return (Var x, t)
         Just (Forall as t) -> do
           ts <- mapM (const newType) as
           return (Var x, instantiate (zip as ts) t)

  Function pat body ->
    do (pt, pat') <- newTypePattern pat
       (body', t) <- bindPattern pat' $ inferE (ln, body)
       return (Function pat' body', tFun pt t)

  Application f v ->
    do (v',fv) <- inferE (ln,v)
       t <- newType
       let ft = tFun fv t
       f' <- checkE ln f ft
       return (Application f' v', t)

  Let dg body ->
    do dg' <- inferDeclGroup dg
       (body', t) <- bindDeclGroup dg' (inferE (ln, body))
       return (Let dg' body', t)

  TSig e t ->
    do t' <- checkKind t
       (e',t'') <- inferE (ln,e)
       unify ln t' t''
       return (e',t'')

  IfThenElse e1 e2 e3 ->
    do e1' <- checkE ln e1 tBool
       (e2', t) <- inferE (ln, e2)
       e3' <- checkE ln e3 t
       return (IfThenElse e1' e2' e3', t)

  LExpr p e ->
    withExprPos p (inferE (ln, e))


checkE :: LName -> Expr -> Type -> TI OutExpr
checkE m e t = do
  (e',t') <- inferE (m,e)
  unify m t t'
  return e'

inferField :: LName -> Bind Expr -> TI (Bind OutExpr,Bind Type)
inferField m (n,e) = do
  (e',t) <- inferE (m,e)
  return ((n,e'),(n,t))

inferDeclGroup :: DeclGroup -> TI DeclGroup
inferDeclGroup (NonRecursive d) = do
  d' <- inferDecl d
  return (NonRecursive d')

inferDeclGroup (Recursive ds) = do
  ds' <- inferRecDecls ds
  return (Recursive ds')

inferStmts :: LName -> Type -> [Stmt] -> TI ([OutStmt], Type)

inferStmts m _ctx [] = do
  recordError ("do block must include at least one expression at " ++ show m)
  t <- newType
  return ([], t)

inferStmts m ctx [StmtBind pos (PWild mt) mc e] = do
  t  <- maybe newType return mt
  e' <- checkE m e (tBlock ctx t)
  mc' <- case mc of
    Nothing -> return ctx
    Just ty  -> do ty' <- checkKind ty
                   unify m ty ctx -- TODO: should this be ty'?
                   return ty'
  return ([StmtBind pos (PWild (Just t)) (Just mc') e'],t)

inferStmts m _ [_] = do
  recordError ("do block must end with expression at " ++ show m)
  t <- newType
  return ([],t)

inferStmts m ctx (StmtBind pos pat mc e : more) = do
  (pt, pat') <- newTypePattern pat
  e' <- checkE m e (tBlock ctx pt)
  mc' <- case mc of
    Nothing -> return ctx
    Just c  -> do c' <- checkKind c
                  unify m c ctx
                  return c'
  (more', t') <- bindPattern pat' $ inferStmts m ctx more

  return (StmtBind pos pat' (Just mc') e' : more', t')

inferStmts m ctx (StmtLet pos dg : more) = do
  dg' <- inferDeclGroup dg
  (more', t) <- bindDeclGroup dg' (inferStmts m ctx more)
  return (StmtLet pos dg' : more', t)

inferStmts m ctx (StmtCode pos s : more) = do
  (more',t) <- inferStmts m ctx more
  return (StmtCode pos s : more', t)

inferStmts m ctx (StmtImport pos imp : more) = do
  (more', t) <- inferStmts m ctx more
  return (StmtImport pos imp : more', t)

inferStmts m ctx (StmtTypedef pos name ty : more) =
  bindTypedef name ty $ do
    (more', t) <- inferStmts m ctx more
    return (StmtTypedef pos name ty : more', t)

patternLNames :: Pattern -> [LName]
patternLNames pat =
  case pat of
    PWild _ -> []
    PVar n _ -> [n]
    PTuple ps -> concatMap patternLNames ps
    LPattern _ pat' -> patternLNames pat'

patternLName :: Pattern -> LName
patternLName pat =
  case patternLNames pat of
    (n : _) -> n
    [] -> Located "_" "_" PosREPL

constrainTypeWithPattern :: LName -> Type -> Pattern -> TI ()
constrainTypeWithPattern ln t pat =
  do (pt, _pat') <- newTypePattern pat
     unify ln t pt

inferDecl :: Decl -> TI Decl
inferDecl (Decl pos pat _ e) = withExprPos pos $ do
  let n = patternLName pat
  (e',t) <- inferE (n, e)
  constrainTypeWithPattern n t pat
  ~[(e1,s)] <- generalize [e'] [t]
  return (Decl pos pat (Just s) e1)

inferRecDecls :: [Decl] -> TI [Decl]
inferRecDecls ds =
  do let pats = map dPat ds
     (_ts, pats') <- unzip <$> mapM newTypePattern pats
     (es, ts) <- fmap unzip
                 $ flip (foldr bindPattern) pats'
                 $ sequence [ withExprPos pos $ inferE (patternLName p, e)
                            | Decl pos p _ e <- ds
                            ]
     sequence_ $ zipWith (constrainTypeWithPattern (error "FIXME")) ts pats'
     ess <- generalize es ts
     return [ Decl pos p (Just s) e1
            | (pos, p, (e1, s)) <- zip3 (map getPos ds) pats ess
            ]

generalize :: [OutExpr] -> [Type] -> TI [(OutExpr,Schema)]
generalize es0 ts0 =
  do es <- appSubstM es0
     ts <- appSubstM ts0

     envUnify <- unifyVarsInEnv
     envNamed <- namedVarsInEnv
     let is = S.toList (unifyVars ts S.\\ envUnify)
     let bs = S.toList (namedVars ts S.\\ envNamed)
     let ns = [ "a." ++ show i | i <- is ]
     let s = listSubst (zip is (map TyVar ns))
     let mk e t = (appSubst s e, Forall (ns ++ bs) (appSubst s t))

     return $ zipWith mk es ts

-- XXX: TODO
checkKind :: Type -> TI Type
checkKind = return



-- }}}


-- Main interface {{{

checkDeclGroup :: Map LName Schema -> Map Name Type -> DeclGroup -> Either [(Pos, String)] DeclGroup
checkDeclGroup env tenv dg =
  case evalTIWithEnv env tenv (getPos dg) (inferDeclGroup dg) of
    Left errs -> Left errs
    Right dg' -> Right dg'

checkDecl :: Map LName Schema -> Map Name Type -> Decl -> Either [(Pos, String)] Decl
checkDecl env tenv decl =
  case evalTIWithEnv env tenv (getPos decl) (inferDecl decl) of
    Left errs -> Left errs
    Right decl' -> Right decl'

evalTIWithEnv :: Map LName Schema -> Map Name Type -> Pos -> TI a -> Either [(Pos, String)] a
evalTIWithEnv env tenv pos m =
  case runTIWithEnv env tenv pos m of
    (res, _, []) -> Right res
    (_, _, errs) -> Left errs

runTIWithEnv :: Map LName Schema -> Map Name Type -> Pos -> TI a -> (a, Subst, [(Pos, String)])
runTIWithEnv env tenv pos m = (a, subst rw, errors rw)
  where
  m' = runReaderT (unTI m) (RO env tenv pos)
  (a,rw) = runState m' emptyRW

-- }}}
