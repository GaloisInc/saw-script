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
-- See Note [-Wincomplete-uni-patterns and irrefutable patterns]
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module SAWScript.MGU
       ( checkDecl
       , checkDeclGroup
       , instantiate
       ) where

import SAWScript.AST
import SAWScript.Panic (panic)
import SAWScript.Position (Inference(..), Pos(..), Positioned(..), choosePos)

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative
#endif

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Identity
import Data.Map (Map)
import Data.Either (partitionEithers)
import qualified Data.Map as M
--import qualified Data.Set as S

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

--
-- Error reporting.
--
-- When we find a mismatch, we have potentially recursed arbitrarily
-- deeply into the original type. We need to print the specific types
-- we trip on (this is important if they are e.g. elements in a large
-- system of nested records and typles) but we also want to print the
-- rest of the original context as well.
--
-- Therefore, we start with an initial descriptive message plus (in
-- most cases) a pair of expected and found types. Once we fail, we
-- add more expected/found type pairs on the way out of the recursion,
-- so we print every layer of the type.
--
-- As a special case, we keep only the outermost of a series of nested
-- function types, and drop the nested ones. Because functions are
-- curried, this prints the complete function signature once and skips
-- the incremental types completed by consuming each argument. (These
-- add little information and can also confuse casual users.)
--
-- The FailMGU type tracks this material. It contains three elements:
--    * the initial message
--    * the list of pairs of expected/found messages
--    * the current function-type expected/found message, if any
--
-- Empty strings are inserted between pairs to make the output more
-- readable.
--
-- Note that we print the messages on the fly rather than accumulating
-- a list of type pairs and printing them at the end. (That may have
-- been a mistake; we'll see.)
--
-- The last element (current function-type expected/found message) is
-- always either a list of two message strings or empty. Function types
-- we see go in it (replacing anything already there, so we keep only
-- the outermost of a series) and are shifted out of it when we see
-- something else. It could be a Maybe (String, String), but the code
-- is noticeably more convenient the way it is.
--
-- The initial message is kept separate so that the expected/found
-- list can readily be built in either order. It's not clear if it's
-- better to print the outermost or innermost mismatches first.
--
-- Further notes on the message formatting:
--
-- Print the expected and found types on their own lines. They can be
-- large; if they are the resulting lines can still be fairly
-- illegible, but at least the user doesn't have to hunt for "found"
-- in the middle of a multi-line print.
--
-- Pad the prefix of the prints so that the types line up; this is
-- helpful for longer types that still fit on one output line.
--
-- We'll indent each line with four spaces. What we send back gets
-- printed underneath a message that's already (at least in some
-- cases) indented by two spaces. It's important to make it clear that
-- all the stuff we generate is part of that message and not, for
-- example, an additional separate error. The indenting happens below.
--
-- Note that although we append to the end of the expected/found list,
-- we don't stick the start line in that list, because I keep going
-- back and forth on whether the larger types should be printed first
-- (prepending in failMGUadd) or last (appending). If we commit to
-- appending we don't need to keep the start line separate.
--

data FailMGU = FailMGU
                    [String]    -- initial error message (often multiple lines)
                    [String]    -- list of found/expected message pairs
                    [String]    -- current found/expected function pair if any

-- common code for printing expected/found types
showTypes :: Type -> Type -> [String]
showTypes ty1 ty2 =
  let expected = "Expected: " ++ pShow ty1
      found    = "Found:    " ++ pShow ty2
  in
  [expected, found, ""]

-- logic for showing details of a type
showTypeDetails :: Type -> String
showTypeDetails ty =
  let pr pos what =
        show pos ++ ": The type " ++ pShow ty ++ " arises from " ++ what
  in
  case getPos ty of
    PosInferred InfFresh pos -> pr pos "fresh type variable introduced here"
    PosInferred InfTerm pos -> pr pos "the type of this term"
    PosInferred InfContext pos -> pr pos "the context of the term"
    pos -> pr pos "this type annotation"

-- fail with expected/found types
failMGU :: String -> Type -> Type -> Either FailMGU a
failMGU start ty1 ty2 = Left (FailMGU start' ("" : showTypes ty1 ty2) [])
  where start' = [start, showTypeDetails ty1, showTypeDetails ty2]

-- fail with no types
failMGU' :: String -> Either FailMGU a
failMGU' start = Left (FailMGU [start] [] [])

-- add another expected/found type pair to the failure
-- (pull in the last function-type lines if any)
failMGUAdd :: FailMGU -> Type -> Type -> FailMGU
failMGUAdd (FailMGU start eflines lastfunlines) ty1 ty2 =
  FailMGU start (eflines ++ lastfunlines ++ showTypes ty1 ty2) []

-- add another pair that's a function type
-- (overwrite any previous function type lines)
failMGUAddFun :: FailMGU -> Type -> Type -> FailMGU
failMGUAddFun (FailMGU start eflines _) ty1 ty2 =
  FailMGU start eflines (showTypes ty1 ty2)

-- print the failure as a string list
ppFailMGU :: FailMGU -> [String]
ppFailMGU (FailMGU start eflines lastfunlines) =
  start ++ eflines ++ lastfunlines

mgu :: Type -> Type -> Either FailMGU Subst
mgu (TyUnifyVar _ i) (TyUnifyVar _ j) | i == j = return emptySubst
mgu (TyUnifyVar pos i) t2 = bindVar pos i t2
mgu t1 (TyUnifyVar pos i) = bindVar pos i t1
mgu r1@(TyRecord _ ts1) r2@(TyRecord _ ts2)
  | M.keys ts1 /= M.keys ts2 =
      failMGU "Record field names mismatch." r1 r2
  | otherwise = case mgus (M.elems ts1) (M.elems ts2) of
      Right result -> Right result
      Left msgs -> Left $ failMGUAdd msgs r1 r2
mgu c1@(TyCon _ tc1 ts1) c2@(TyCon _ tc2 ts2)
  | tc1 == tc2 = case mgus ts1 ts2 of
      Right result -> Right result
      Left msgs ->
        case tc1 of
          FunCon -> Left $ failMGUAddFun msgs c1 c2
          _ -> Left $ failMGUAdd msgs c1 c2
  | otherwise = case tc1 of
      FunCon ->
        failMGU "Term is not a function. (Maybe a function is applied to too many arguments?)" c1 c2
      _ ->
        failMGU ("Mismatch of type constructors. Expected: " ++ pShow tc1 ++ " but got " ++ pShow tc2) c1 c2
mgu (TyVar _ a) (TyVar _ b)
  | a == b = return emptySubst
mgu t1 t2 = failMGU "Mismatch of types." t1 t2

mgus :: [Type] -> [Type] -> Either FailMGU Subst
mgus [] [] = return emptySubst
mgus (t1:ts1) (t2:ts2) = do
  s <- mgu t1 t2
  s' <- mgus (map (appSubst s) ts1) (map (appSubst s) ts2)
  return (s' @@ s)
mgus ts1 ts2 =
  failMGU' $ "Wrong number of arguments. Expected " ++ show (length ts1) ++ " but got " ++ show (length ts2)

-- Does not handle the case where t _is_ TyUnifyVar i; the caller handles that
bindVar :: Pos -> TypeIndex -> Type -> Either FailMGU Subst
bindVar pos i t =
  case M.lookup i $ unifyVars t of
     Just otherpos ->
       -- FIXME/XXX: this error message is better than the one that was here before
       -- but still lacks a certain something
       failMGU' $ "Occurs check failure: the type at " ++ show otherpos ++
                  " appears within the type at " ++ show pos
     Nothing ->
       return (singletonSubst i t)

-- }}}

-- UnifyVars {{{

-- unifyVars is a type-class-polymorphic function for extracting
-- unification vars from a type or type schema. It returns a set of
-- TypeIndex (TypeIndex is just Integer) manifested as a map from
-- those TypeIndexes to their positions/provenance.
class UnifyVars t where
  unifyVars :: t -> M.Map TypeIndex Pos

instance (Ord k, UnifyVars a) => UnifyVars (M.Map k a) where
  unifyVars = unifyVars . M.elems

instance (UnifyVars a) => UnifyVars [a] where
  unifyVars = M.unionsWith choosePos . map unifyVars

instance UnifyVars Type where
  unifyVars t = case t of
    TyCon _ _ ts      -> unifyVars ts
    TyRecord _ tm     -> unifyVars tm
    TyVar _ _         -> M.empty
    TyUnifyVar pos i  -> M.singleton i pos

instance UnifyVars Schema where
  unifyVars (Forall _ t) = unifyVars t

-- }}}

-- NamedVars {{{

-- namedVars is a type-class-polymorphic function for extracting named
-- type variables from a type or type schema. It returns a set of Name
-- (Name is just String) manifested as a map from those Names to their
-- positions/provenance.
class NamedVars t where
  namedVars :: t -> M.Map Name Pos

instance (Ord k, NamedVars a) => NamedVars (M.Map k a) where
  namedVars = namedVars . M.elems

instance (NamedVars a) => NamedVars [a] where
  namedVars = M.unionsWith choosePos . map namedVars

instance NamedVars Type where
  namedVars t = case t of
    TyCon _ _ ts      -> namedVars ts
    TyRecord _ tm     -> namedVars tm
    TyVar pos n       -> M.singleton n pos
    TyUnifyVar _ _    -> M.empty

instance NamedVars Schema where
  namedVars (Forall ns t) = namedVars t M.\\ M.fromList ns'
    where ns' = map (\(pos, n) -> (n, pos)) ns

-- }}}

-- TI Monad {{{

newtype TI a = TI { unTI :: ReaderT RO (StateT RW Identity) a }
                        deriving (Functor,Applicative,Monad,MonadReader RO)

data RO = RO
  { typeEnv :: M.Map (Located Name) Schema
  , typedefEnv :: M.Map Name Type
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

-- Construct a new type variable.
--
-- Collect the position that prompted us to make it; for example, if
-- we're the element type of an empty list we get the position of the
-- []. We haven't inferred anything, so use the InfFresh position.
-- This will cause the position of anything more substantive that gets
-- unified with it to be preferred. If no such thing happens though
-- this will be the position that gets attached to the quantifier
-- binding in generalize.
newType :: Pos -> TI Type
newType pos = TyUnifyVar (PosInferred InfFresh pos) <$> newTypeIndex

-- Construct a new type variable to use as a placeholder after an
-- error occurs. For now this is the same as other fresh type
-- variables, but I've split it out in case we want to distinguish it
-- in the future.
newTypeError :: Pos -> TI Type
newTypeError pos = newType pos

-- Typecheck a pattern and produce fresh type variables as needed.
-- FUTURE: this function should get renamed.
newTypePattern :: Pattern -> TI (Type, Pattern)
newTypePattern pat =
  case pat of
    PWild pos mt ->
      do t <- maybe (newType pos) return mt
         return (t, PWild pos (Just t))
    PVar pos x mt ->
      do t <- maybe (newType pos) return mt
         return (t, PVar pos x (Just t))
    PTuple pos ps ->
      do (ts, ps') <- unzip <$> mapM newTypePattern ps
         return (tTuple (PosInferred InfTerm pos) ts, PTuple pos ps')

appSubstM :: AppSubst t => t -> TI t
appSubstM t = do
  s <- TI $ gets subst
  return $ appSubst s t

recordError :: Pos -> String -> TI ()
recordError pos err = do
  TI $ modify $ \rw -> rw { errors = (pos, err) : errors rw }

--
-- Unify two types.
--

-- When typechecking an expression the first type argument (t1) should
-- be the type expected from the context, and the second (t2) should
-- be the type found in the expression appearing in that context. For
-- example, when checking the second argument of a function application
-- (Application _pos e1 e2) checking e1 gives rise to an expected type
-- for e2, so when unifying that with the result of checking e2 the
-- t1 argument should be the expected type arising from e1, the t2
-- argument should be the type returned by checking e2, and the position
-- argument should be the position of e2 (not the position of the
-- enclosing apply node). If it doesn't work, the message generated
-- will be of the form "pos: found t2, expected t1".
--
-- Other cases should pass the arguments analogously. As of this
-- writing some are definitely backwards.
--
-- Further notes on error messages:
--
-- The error message returned by mgu already prints the types at some
-- length, so we don't need to print any of that again.
--
-- Indent all but the first line by four spaces because the first line
-- ends up indented by two when it ultimately gets printed (or at
-- least sometimes it does) and we want the grouping to be clearly
-- recognizable.
--
-- The LName passed in is (at least in most cases) the name of the
-- top-level binding the unification happens inside. Its position is
-- therefore usually not where the problem is except in a very
-- abstract sense and shouldn't be printed as if it's the error
-- location. So tack it onto the end of everything.
--
-- It's not clear that this is always the case, so in turn it's not
-- entirely clear that it's always useless and I'm hesitant to remove
-- it entirely, but that seems like a reasonable thing to do in the
-- future given more clarity.
--
unify :: LName -> Type -> Pos -> Type -> TI ()
unify m t1 pos t2 = do
  t1' <- appSubstM =<< instantiateM t1
  t2' <- appSubstM =<< instantiateM t2
  case mgu t1' t2' of
    Right s -> TI $ modify $ \rw -> rw { subst = s @@ subst rw }
    Left msgs ->
       recordError pos $ unlines $ firstline : morelines'
       where
         firstline = "Type mismatch."
         morelines = ppFailMGU msgs ++ ["within " ++ show m]
         -- Indent all but the first line by four spaces.
         morelines' = map (\msg -> "    " ++ msg) morelines

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
    PWild _ _mt -> []
    PVar _ x mt -> [(x, mt)]
    PTuple _ ps -> concatMap patternBindings ps

bindPatternSchema :: Pattern -> Schema -> TI a -> TI a
bindPatternSchema pat s@(Forall vs t) m =
  case pat of
    PWild _ _ -> m
    PVar _ n _ -> bindSchema n s m
    PTuple _ ps ->
      case t of
        TyCon _pos (TupleCon _) ts -> foldr ($) m
          [ bindPatternSchema p (Forall vs t') | (p, t') <- zip ps ts ]
        _ -> m

bindTypedef :: LName -> Type -> TI a -> TI a
bindTypedef n t m =
  TI $
  local
    (\ro ->
      let t' = instantiate (typedefEnv ro) t
      in  ro { typedefEnv = M.insert (getVal n) t' $ typedefEnv ro })
    $ unTI m

-- FIXME: This function may miss type variables that occur in the type
-- of a binding that has been shadowed by another value with the same
-- name. This could potentially cause a run-time type error if the
-- type of a local function gets generalized too much. We can probably
-- wait to fix it until someone finds a sawscript program that breaks.
unifyVarsInEnv :: TI (M.Map TypeIndex Pos)
unifyVarsInEnv = do
  env <- TI $ asks typeEnv
  let ss = M.elems env
  ss' <- mapM appSubstM ss
  return $ unifyVars ss'

namedVarsInEnv :: TI (M.Map Name Pos)
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
    TyCon pos tc ts     -> TyCon pos tc (appSubst s ts)
    TyRecord pos fs     -> TyRecord pos (appSubst s fs)
    TyVar _ _           -> t
    TyUnifyVar _ i      -> case M.lookup i (unSubst s) of
                             Just t' -> t'
                             Nothing -> t

instance AppSubst Schema where
  appSubst s (Forall ns t) = Forall ns (appSubst s t)

instance AppSubst Expr where
  appSubst s expr = case expr of
    TSig pos e t           -> TSig pos (appSubst s e) (appSubst s t)
    Bool _ _               -> expr
    String _ _             -> expr
    Int _ _                -> expr
    Code _                 -> expr
    CType _                -> expr
    Array pos es           -> Array pos (appSubst s es)
    Block pos bs           -> Block pos (appSubst s bs)
    Tuple pos es           -> Tuple pos (appSubst s es)
    Record pos fs          -> Record pos (appSubst s fs)
    Index pos ar ix        -> Index pos (appSubst s ar) (appSubst s ix)
    Lookup pos rec fld     -> Lookup pos (appSubst s rec) fld
    TLookup pos tpl idx    -> TLookup pos (appSubst s tpl) idx
    Var _                  -> expr
    Function pos pat body  -> Function pos (appSubst s pat) (appSubst s body)
    Application pos f v    -> Application pos (appSubst s f) (appSubst s v)
    Let pos dg e           -> Let pos (appSubst s dg) (appSubst s e)
    IfThenElse pos e e2 e3 -> IfThenElse pos (appSubst s e) (appSubst s e2) (appSubst s e3)

instance AppSubst Pattern where
  appSubst s pat = case pat of
    PWild pos mt  -> PWild pos (appSubst s mt)
    PVar pos x mt -> PVar pos x (appSubst s mt)
    PTuple pos ps -> PTuple pos (appSubst s ps)

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
  -- | @instantiate m x@ applies the map @m@ to type variables in @x@.
  instantiate :: Map Name Type -> t -> t

instance (Instantiate a) => Instantiate (Maybe a) where
  instantiate nts = fmap (instantiate nts)

instance (Instantiate a) => Instantiate [a] where
  instantiate nts = map (instantiate nts)

instance Instantiate Type where
  instantiate nts ty = case ty of
    TyCon pos tc ts     -> TyCon pos tc (instantiate nts ts)
    TyRecord pos fs     -> TyRecord pos (fmap (instantiate nts) fs)
    TyVar _ n           -> M.findWithDefault ty n nts
    TyUnifyVar _ _      -> ty

instantiateM :: Instantiate t => t -> TI t
instantiateM t = do
  s <- TI $ asks typedefEnv
  return $ instantiate s t

-- }}}

-- Type Inference {{{

type OutExpr = Expr
type OutStmt = Stmt

inferE :: (LName, Expr) -> TI (OutExpr,Type)
inferE (ln, expr) = case expr of
  Bool pos b    -> return (Bool pos b, tBool (PosInferred InfTerm pos))
  String pos s  -> return (String pos s, tString (PosInferred InfTerm pos))
  Int pos i     -> return (Int pos i, tInt (PosInferred InfTerm pos))
  Code s        -> return (Code s, tTerm (PosInferred InfTerm $ getPos s))
  CType s       -> return (CType s, tType (PosInferred InfTerm $ getPos s))

  Array pos [] ->
    do a <- newType pos
       return (Array pos [], tArray (PosInferred InfTerm pos) a)

  Array pos (e:es) ->
    do (e',t) <- inferE (ln, e)
       es' <- mapM (flip (checkE ln) t) es
       return (Array pos (e':es'), tArray (PosInferred InfTerm pos) t)

  Block pos bs ->
    do ctx <- newType pos
       (bs',t') <- inferStmts ln pos ctx bs
       return (Block pos bs', tBlock (PosInferred InfTerm pos) ctx t')

  Tuple pos es ->
    do (es',ts) <- unzip `fmap` mapM (inferE . (ln,)) es
       return (Tuple pos es', tTuple (PosInferred InfTerm pos) ts)

  Record pos fs ->
    do (nes',nts) <- unzip `fmap` mapM (inferField ln) (M.toList fs)
       let ty = TyRecord (PosInferred InfTerm pos) $ M.fromList nts
       return (Record pos (M.fromList nes'), ty)

  Index pos ar ix ->
    do (ar',at) <- inferE (ln,ar)
       ix'      <- checkE ln ix (tInt (PosInferred InfContext (getPos ix)))
       t        <- newType (getPos ix')
       unify ln (tArray (PosInferred InfContext (getPos ar')) t) (getPos ar') at
       return (Index pos ar' ix', t)

  Lookup pos e n ->
    do (e1,t) <- inferE (ln, e)
       t1 <- appSubstM =<< instantiateM t
       elTy <- case t1 of
                 TyRecord typos fs
                    | Just ty <- M.lookup n fs -> return ty
                    | otherwise ->
                          do recordError pos $ unlines
                                [ "Selecting a missing field."
                                , "Field name: " ++ n
                                ]
                             newTypeError typos
                 _ -> do recordError pos $ unlines
                            [ "Record lookup on non-record argument."
                            , "Field name: " ++ n
                            ]
                         newTypeError pos
       return (Lookup pos e1 n, elTy)

  TLookup pos e i ->
    do (e1,t) <- inferE (ln,e)
       t1 <- appSubstM =<< instantiateM t
       elTy <- case t1 of
                 TyCon typos (TupleCon n) tys
                   | i < n -> return (tys !! fromIntegral i)
                   | otherwise ->
                          do recordError pos $ unlines
                                [ "Tuple index out of bounds."
                                , "Given index " ++ show i ++
                                  " is too large for tuple size of " ++
                                  show n
                                ]
                             newTypeError typos
                 _ -> do recordError pos $ unlines
                            [ "Tuple lookup on non-tuple argument."
                            , "Given index " ++ show i
                            ]
                         newTypeError pos
       return (TLookup pos e1 i, elTy)

  Var x ->
    do env <- TI $ asks typeEnv
       case M.lookup x env of
         Nothing -> do
           recordError (getPos x) $ unlines
             [ "Unbound variable: " ++ show x
             , "Note that some built-in commands are available only after running"
             , "either `enable_deprecated` or `enable_experimental`."
             ]
           t <- newType (getPos x)
           return (Var x, t)
         Just (Forall as t) -> do
           -- get a fresh tyvar for each quantifier binding, convert
           -- to a name -> ty map, and instantiate with the fresh tyvars
           let once (apos, a) = do
                 at <- newType apos
                 return (a, at)
           substs <- mapM once as
           let t' = instantiate (M.fromList substs) t
           return (Var x, t')

  Function pos pat body ->
    do (pt, pat') <- newTypePattern pat
       (body', t) <- bindPattern pat' $ inferE (ln, body)
       return (Function pos pat' body', tFun (PosInferred InfContext (getPos body)) pt t)

  Application pos f v ->
    do (v',fv) <- inferE (ln,v)
       t <- newType pos
       let ft = tFun (PosInferred InfContext $ getPos f) fv t
       f' <- checkE ln f ft
       return (Application pos f' v', t)

  Let pos dg body ->
    do dg' <- inferDeclGroup dg
       (body', t) <- bindDeclGroup dg' (inferE (ln, body))
       return (Let pos dg' body', t)

  TSig _pos e t ->
    do t' <- checkKind t
       (e',t'') <- inferE (ln,e)
       unify ln t' (getPos e') t''
       return (e',t'')

  IfThenElse pos e1 e2 e3 ->
    do e1' <- checkE ln e1 (tBool (PosInferred InfContext $ getPos e1))
       (e2', t) <- inferE (ln, e2)
       e3' <- checkE ln e3 t
       return (IfThenElse pos e1' e2' e3', t)


checkE :: LName -> Expr -> Type -> TI OutExpr
checkE m e t = do
  (e',t') <- inferE (m,e)
  unify m t (getPos e') t'
  return e'

-- Take a struct field binding (name and expression) and return the
-- updated binding as well as the member entry for the enclosing
-- struct type.
inferField :: LName -> (Name, Expr) -> TI ((Name, OutExpr), (Name, Type))
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

-- the passed-in position should be the position for the whole statement block
-- the first type argument (ctx) is ... XXX
inferStmts :: LName -> Pos -> Type -> [Stmt] -> TI ([OutStmt], Type)

inferStmts m pos _ctx [] = do
  recordError pos ("do block must include at least one expression at " ++ show m)
  t <- newTypeError pos
  return ([], t)

inferStmts m dopos ctx [StmtBind spos (PWild patpos mt) mc e] = do
  t  <- maybe (newType patpos) return mt
  e' <- checkE m e (tBlock dopos ctx t)
  mc' <- case mc of
    Nothing -> return ctx
    Just ty  -> do ty' <- checkKind ty
                   -- dholland 20240628 are the type arguments backwards? thought
                   -- so at first but now I'm not sure. Also I'm not sure this is
                   -- the right position to use. Where does mc come from? Is it a
                   -- source annotation? If so it should probably have its own
                   -- position. XXX
                   unify m ty (getPos e) ctx -- TODO: should this be ty'?
                   return ty'
  return ([StmtBind spos (PWild patpos (Just t)) (Just mc') e'],t)

inferStmts m dopos _ [_] = do
  recordError dopos ("do block must end with expression at " ++ show m)
  t <- newTypeError dopos
  return ([],t)

inferStmts m dopos ctx (StmtBind spos pat mc e : more) = do
  (pt, pat') <- newTypePattern pat
  e' <- checkE m e (tBlock dopos ctx pt)
  mc' <- case mc of
    Nothing -> return ctx
    Just c  -> do c' <- checkKind c
                  -- XXX same as above
                  unify m c (getPos e) ctx
                  return c'
  (more', t') <- bindPattern pat' $ inferStmts m dopos ctx more

  return (StmtBind spos pat' (Just mc') e' : more', t')

inferStmts m dopos ctx (StmtLet spos dg : more) = do
  dg' <- inferDeclGroup dg
  (more', t) <- bindDeclGroup dg' (inferStmts m dopos ctx more)
  return (StmtLet spos dg' : more', t)

inferStmts m dopos ctx (StmtCode spos s : more) = do
  (more',t) <- inferStmts m dopos ctx more
  return (StmtCode spos s : more', t)

inferStmts m dopos ctx (StmtImport spos imp : more) = do
  (more', t) <- inferStmts m dopos ctx more
  return (StmtImport spos imp : more', t)

inferStmts m dopos ctx (StmtTypedef spos name ty : more) =
  bindTypedef name ty $ do
    (more', t) <- inferStmts m dopos ctx more
    return (StmtTypedef spos name ty : more', t)

-- Get the position and name of the first binding in a pattern,
-- for use as context info when printing messages. If there's a
-- real variable, prefer that (Right cases); otherwise take the
-- position of the first wildcard or empty tuple (Left cases).
patternLName :: Pattern -> LName
patternLName pat0 =
  case visit pat0 of
    Left pos -> Located "_" "_" pos
    Right n -> n
  where
    visit pat =
      case pat of
        PWild pos _ -> Left pos
        PVar _ n _ -> Right n
        PTuple pos [] -> Left pos
        PTuple allpos ps ->
          case partitionEithers $ map visit ps of
             (_, n : _) -> Right n
             (pos : _, _) -> Left pos
             _ -> Left allpos

constrainTypeWithPattern :: LName -> Type -> Pattern -> TI ()
constrainTypeWithPattern ln t pat =
  do (pt, _pat') <- newTypePattern pat
     unify ln t (getPos pat) pt

inferDecl :: Decl -> TI Decl
inferDecl (Decl pos pat _ e) = do
  let n = patternLName pat
  (e',t) <- inferE (n, e)
  constrainTypeWithPattern n t pat
  ~[(e1,s)] <- generalize [e'] [t]
  return (Decl pos pat (Just s) e1)

inferRecDecls :: [Decl] -> TI [Decl]
inferRecDecls ds =
  do let pats = map dPat ds
         pat =
           case pats of
             p:_ -> p
             [] -> panic
                     "inferRecDecls"
                     ["Empty list of declarations in recursive group"]
     (_ts, pats') <- unzip <$> mapM newTypePattern pats
     (es, ts) <- fmap unzip
                 $ flip (foldr bindPattern) pats'
                 $ sequence [ inferE (patternLName p, e)
                            | Decl _pos p _ e <- ds
                            ]
     sequence_ $ zipWith (constrainTypeWithPattern (patternLName pat)) ts pats'
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
     let is = M.toList (unifyVars ts M.\\ envUnify)
     let bs = M.toList (namedVars ts M.\\ envNamed)

     -- if the position is "fresh" turn it into "inferred from term"
     let adjustPos pos = case pos of
           PosInferred InfFresh pos' -> PosInferred InfTerm pos'
           _ -> pos

     -- generate names for the unification vars
     let is' = [ (i, adjustPos pos, "a." ++ show i) | (i, pos) <- is ]

     -- build the substitution
     let s = listSubst [ (i, TyVar pos n) | (i, pos, n) <- is' ]

     -- get the names for the Forall
     let inames = [ (pos, n) | (_i, pos, n) <- is' ]
     let bnames = [ (pos, x) | (x, pos) <- bs ]

     let mk e t = (appSubst s e, Forall (inames ++ bnames) (appSubst s t))

     return $ zipWith mk es ts

-- XXX: TODO
checkKind :: Type -> TI Type
checkKind = return



-- }}}


-- Main interface {{{

checkDeclGroup :: Map LName Schema -> Map Name Type -> DeclGroup -> Either [(Pos, String)] DeclGroup
checkDeclGroup env tenv dg =
  case evalTIWithEnv env tenv (inferDeclGroup dg) of
    Left errs -> Left errs
    Right dg' -> Right dg'

checkDecl :: Map LName Schema -> Map Name Type -> Decl -> Either [(Pos, String)] Decl
checkDecl env tenv decl =
  case evalTIWithEnv env tenv (inferDecl decl) of
    Left errs -> Left errs
    Right decl' -> Right decl'

evalTIWithEnv :: Map LName Schema -> Map Name Type -> TI a -> Either [(Pos, String)] a
evalTIWithEnv env tenv m =
  case runTIWithEnv env tenv m of
    (res, _, []) -> Right res
    (_, _, errs) -> Left errs

runTIWithEnv :: Map LName Schema -> Map Name Type -> TI a -> (a, Subst, [(Pos, String)])
runTIWithEnv env tenv m = (a, subst rw, errors rw)
  where
  m' = runReaderT (unTI m) (RO env tenv)
  (a,rw) = runState m' emptyRW

-- }}}

{-
Note [-Wincomplete-uni-patterns and irrefutable patterns]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Various parts of SAW use irrefutable patterns in functions that assume that
their arguments have particular shapes. For example, inferDecl in this module
matches on ~[(e1,s)] with an irrefutable pattern because it assumes the
invariant that the list will have exactly one element. This lets inferDecl be
slightly lazier when evaluated.

Unfortunately, this use of irrefutable patterns is at odds with the
-Wincomplete-uni-patterns warning. At present, -Wincomplete-uni-patterns will
produce a warning for any irrefutable pattern that does not cover all possible
data constructors. While we could rewrite functions like `inferDecl` to
explicitly provide a fall-through case, that would change its strictness
properties. As a result, we simply disable -Wincomplete-uni-patterns warnings
in each part of SAW that uses irrefutable patterns.

Arguably, -Wincomplete-uni-patterns shouldn't be producing warnings for
irrefutable patterns at all. GHC issue #14800
(https://gitlab.haskell.org/ghc/ghc/-/issues/14800) proposes this idea.
If that issue is fixed in the future, we may want to reconsider whether we want
to disable -Wincomplete-uni-patterns.
-}
