{- |
Module      : SAWScript.MGU
Description : SAW-Script type checking.
License     : BSD3
Maintainer  : diatchki
Stability   : provisional
-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TupleSections #-}
-- See Note [-Wincomplete-uni-patterns and irrefutable patterns]
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module SAWScript.MGU
       ( checkDecl
       , checkStmt
       , instantiate
       ) where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative
#endif

import Control.Monad (zipWithM)
import Control.Monad.Reader (MonadReader(..), ReaderT(..), asks)
import Control.Monad.State (MonadState(..), StateT, gets, modify, runState)
import Control.Monad.Identity (Identity)
import qualified Data.Text as Text
import Data.List (intercalate, genericTake)
import Data.Map (Map)
import Data.Either (partitionEithers)
import qualified Data.Map as M
import qualified Data.Set as S

import qualified Prettyprinter as PP

import SAWScript.AST
import SAWScript.ASTUtil (namedVars)
import SAWScript.Panic (panic)
import SAWScript.Position (Inference(..), Pos(..), Positioned(..), choosePos)

-- should probably move this to AST
tUnit :: Pos -> Type
tUnit pos = tTuple pos []


-- short names for the environment types we use
type VarEnv = Map LName Schema
type TyEnv = Map Name NamedType 


------------------------------------------------------------
-- UnifyVars {{{

--
-- unifyVars is a type-class-polymorphic function for extracting
-- unification vars from a type or type schema. It returns a set of
-- TypeIndex (TypeIndex is just Integer) manifested as a map from
-- those TypeIndexes to their positions/provenance.
--

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

instance UnifyVars NamedType where
  unifyVars nt = case nt of
    ConcreteType ty -> unifyVars ty
    AbstractType -> M.empty

-- }}}


------------------------------------------------------------
-- Substitutions {{{

-- Subst is the type of a substitution map for unification vars.
newtype Subst = Subst { unSubst :: M.Map TypeIndex Type } deriving (Show)

-- Merge two substitution maps.
--
-- XXX: this knows that in the uses below the right substitution (m1)
-- is the older/preexisting one. That probably shouldn't be silently
-- baked in.
--
-- We apply the left substitution (m2) into the types in the right
-- substitution (m1). That is, any new substitutions are applied into
-- the existing ones. I expect this in pursuit of an invariant where
-- any unification variables existing in the right-hand sides of the
-- substitution aren't themselves defined by the substitution, so we
-- don't have to recurse into the right-hand sides later when applying
-- the substitution.
--
-- XXX: However, this assumes that whatever is on the left-hand side
-- doesn't already violate this invariant. We can check this with
-- reasonable accuracy since we have right here all the ways to create
-- a Subst (and we can check that there aren't any others hidden
-- below)... and we find that while emptySubst is obviously ok, and
-- singletonSubst is ok (an attempt to create a singleton substitution
-- that refers to itself will fail the occurs check right before
-- calling singletonSubst), there doesn't seem to be any such
-- assurance for substFromList. I'm not sure if this is actually a
-- problem or not but it should probably be looked into at some point.
--
-- XXX: we should probably crosscheck the key space of the maps. Note
-- that the ordering of the M.union args means that if there are
-- duplicated keys we prefer the right substitution (m1), namely the
-- preexisting one. Given that this choice seems to be explicit, it
-- must have been for a reason, but I'm not sure what that reason
-- would be. Ordinarily in this kind of typechecker you might update a
-- substitution you've already made, but only when replacing a weak
-- substitution (one unification var for another, like a1 -> a2) with
-- a strong one (involving a real type, like a1 -> Int)... but if so
-- it would always be the _new_ substitution you'd want to keep.
-- However, in this particular code we always apply the existing
-- substitution before doing further unification, so once we have any
-- substitution for a given unification var we shouldn't get another.
-- (Unless I guess if the intended invariant above is violated, but if
-- that happens we should probably panic, not chug along.)
--
-- XXX: also it isn't clear that anything below guarantees that we
-- won't just derive multiple inconsistent substitutions (e.g. from
-- disjoint subexpressions) and combine them incoherently. This should
-- really be looked into further.
--
-- XXX: and _furthermore_ it's not clear that we can't get cyclic
-- substitutions. If we already have a substitution a1 -> a2, and we
-- add a2 -> a1, we'll resolve the existing substitution to a1 -> a1
-- rather than going directly into an infinite loop. That's not
-- necessarily preferable though. Normally in this kind of typechecker
-- one also wants some kind of acyclicity-oriented invariant, like
-- aN resolves to aM only if N > M (otherwise you substitute the other
-- way) but we don't do anything like that.
--
-- When all the above issues get clarified we should consider coming
-- up with a different name that indicates that this operation isn't
-- commutative. Unless it actually can be.
mergeSubst :: Subst -> Subst -> Subst
mergeSubst s2@(Subst m2) (Subst m1) = Subst $ m1' `M.union` m2
  where
  m1' = fmap (appSubst s2) m1

emptySubst :: Subst
emptySubst = Subst M.empty

singletonSubst :: TypeIndex -> Type -> Subst
singletonSubst tv t = Subst $ M.singleton tv t

substFromList :: [(TypeIndex, Type)] -> Subst
substFromList entries = Subst $ M.fromList entries

--
-- appSubst is a type-class-polymorphic function for applying a
-- substitution (of numbered unification vars) to AST elements.
--

class AppSubst t where
  appSubst :: Subst -> t -> t

instance (AppSubst t) => AppSubst (Maybe t) where
  appSubst s = fmap $ appSubst s

instance (AppSubst t) => AppSubst [t] where
  appSubst s = map $ appSubst s

instance (Ord k, AppSubst a) => AppSubst (M.Map k a) where
  appSubst s = fmap (appSubst s)

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

instance AppSubst Stmt where
  appSubst s bst = case bst of
    StmtBind pos pat e       -> StmtBind pos (appSubst s pat) (appSubst s e)
    StmtLet pos dg           -> StmtLet pos (appSubst s dg)
    StmtCode pos str         -> StmtCode pos str
    StmtImport pos imp       -> StmtImport pos imp
    StmtTypedef pos name ty  -> StmtTypedef pos name (appSubst s ty)

instance AppSubst DeclGroup where
  appSubst s (Recursive ds) = Recursive (appSubst s ds)
  appSubst s (NonRecursive d) = NonRecursive (appSubst s d)

instance AppSubst Decl where
  appSubst s (Decl pos p mt e) = Decl pos (appSubst s p) (appSubst s mt) (appSubst s e)

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

instance AppSubst NamedType where
  appSubst s nt = case nt of
    ConcreteType ty -> ConcreteType $ appSubst s ty
    AbstractType -> AbstractType

-- }}}


------------------------------------------------------------
-- Instantiate {{{

--
-- instantiate is a typeclass-polymorphic function for substituting
-- named type variables (such as those declared with typedef) in a
-- Type.
--
-- Note: instantiate is exposed from this module and reused by the
-- interpreter as part of its handling of typedefs during execution.
-- XXX: Should probably come up with a clearer name. "instantiate"
-- could mean just about anything...
--

class Instantiate t where
  -- | @instantiate m x@ applies the map @m@ to type variables in @x@.
  instantiate :: TyEnv -> t -> t

instance (Instantiate a) => Instantiate (Maybe a) where
  instantiate tyenv = fmap (instantiate tyenv)

instance (Instantiate a) => Instantiate [a] where
  instantiate tyenv = map (instantiate tyenv)

instance Instantiate Type where
  instantiate tyenv ty = case ty of
    TyCon pos tc ts     -> TyCon pos tc (instantiate tyenv ts)
    TyRecord pos fs     -> TyRecord pos (fmap (instantiate tyenv) fs)
    TyUnifyVar _ _      -> ty
    TyVar _ n           ->
        case M.lookup n tyenv of
            Nothing -> ty
            Just AbstractType -> ty
            Just (ConcreteType ty') -> ty'

-- }}}


------------------------------------------------------------
-- Kinds {{{

--
-- For the time being we can handle kinds using the number of expected
-- type arguments. That is, Kind 0 is *. Apart from tuples the only
-- things we have are of kinds *, * -> *, and * -> * -> *, but we do
-- have tuples of arbitrary arity.
--
-- If we ever want additional structure (e.g. distinguishing the
-- monad/context types from other types) we can extend this
-- representation easily enough.
--

newtype Kind = Kind { kindNumArgs :: Int }
  deriving Eq

kindStar :: Kind
kindStar = Kind 0

-- these aren't currently used
--kindStarToStar :: Kind
--kindStarToStar = Kind 1
--
--kindStarToStarToStar :: Kind
--kindStarToStarToStar = Kind 2

instance PrettyPrint Kind where
  pretty _ (Kind n) =
     PP.viaShow $ intercalate " -> " $ take (n + 1) $ repeat "*"


-- }}}


------------------------------------------------------------
-- Pass context {{{

--
-- The monad for this pass is "TI", which is composed of a "readonly"
-- part (which is not constant or readonly, but where changes are
-- scoped by the recursive structure of the code) and a read-write
-- part that accumulates as we move through the code.
--
-- XXX: the "readonly" part is used to implement scoping, which is
-- fine in theory, but in practice because we have declarations that
-- update the environment, the recursive structure of the code does
-- not naturally match the scoping. The result is that the recursive
-- structure of the code has been twisted around to make it work;
-- that isn't desirable and the organization should probably be
-- revised.
--
-- Anyhow, the elements of the context are split across RO and RW
-- below.
--

newtype TI a = TI { unTI :: ReaderT RO (StateT RW Identity) a }
                        deriving (Functor,Applicative,Monad,MonadReader RO)

-- | The "readonly" portion
data RO = RO
  {
    -- | The variable typing environment (variable name to type scheme)
    varEnv :: VarEnv,

    -- | The type environment: named type variables, which are either
    --   typedefs (map to ConcreteType) or abstract types (AbstractType)
    tyEnv :: TyEnv
  }

-- | The read-write portion
data RW = RW
  {
    -- | The next fresh unification var number
    nextTypeIndex :: TypeIndex,

    -- | The unification var substitution we're accumulating
    subst :: Subst,

    -- | Any type errors and warnings we've generated so far
    errors :: [(Pos, String)],
    warnings :: [(Pos, String)]
  }

emptyRW :: RW
emptyRW = RW
  { nextTypeIndex = 0
  , subst = emptySubst
  , errors = []
  , warnings = []
  }

-- Get a fresh unification var number.
getFreshTypeIndex :: TI TypeIndex
getFreshTypeIndex = do
  rw <- TI get
  TI $ put $ rw { nextTypeIndex = nextTypeIndex rw + 1 }
  return $ nextTypeIndex rw

-- Construct a fresh type variable.
--
-- Collect the position that prompted us to make it; for example, if
-- we're the element type of an empty list we get the position of the
-- []. We haven't inferred anything, so use the InfFresh position.
-- This will cause the position of anything more substantive that gets
-- unified with it to be preferred. If no such thing happens though
-- this will be the position that gets attached to the quantifier
-- binding in generalize.
getFreshTyVar :: Pos -> TI Type
getFreshTyVar pos = TyUnifyVar (PosInferred InfFresh pos) <$> getFreshTypeIndex

-- Construct a new type variable to use as a placeholder after an
-- error occurs. For now this is the same as other fresh type
-- variables, but I've split it out in case we want to distinguish it
-- in the future.
getErrorTyVar :: Pos -> TI Type
getErrorTyVar pos = getFreshTyVar pos

-- Add an error message.
recordError :: Pos -> String -> TI ()
recordError pos err = do
  TI $ modify $ \rw -> rw { errors = (pos, err) : errors rw }

-- Add a warning message.
recordWarning :: Pos -> String -> TI ()
recordWarning pos msg = do
  TI $ modify $ \rw -> rw { warnings = (pos, msg) : warnings rw }

-- Apply the current substitution with appSubst.
applyCurrentSubst :: AppSubst t => t -> TI t
applyCurrentSubst t = do
  s <- TI $ gets subst
  return $ appSubst s t

-- Apply the current typedef collection with instantiate.
resolveCurrentTypedefs :: Instantiate t => t -> TI t
resolveCurrentTypedefs t = do
  s <- TI $ asks tyEnv
  return $ instantiate s t

-- Get the unification vars that are used in the current variable typing
-- and named type environments.
--
-- FIXME: This function may miss type variables that occur in the type
-- of a binding that has been shadowed by another value with the same
-- name. This could potentially cause a run-time type error if the
-- type of a local function gets generalized too much. We can probably
-- wait to fix it until someone finds a sawscript program that breaks.
--
-- dholland 20241220: I don't think that's a problem. If there's a
-- loose unification var somewhere that's been shadowed to the point
-- where it's not accessible, we can't have accessed it in order to
-- generate a reference to it in the current block. If it is somewhere
-- accessible, we'll find it there. This might have broken in the past
-- when it didn't search the named type environment, but that leak has
-- been corrected.
--
-- Note that we apply the current substitution first. This means that
-- the caller must also apply the current substitution before reasoning
-- about what unification vars do and don't appear.
--
-- Returns a map of the index number to the occurrence position.
unifyVarsInEnvs :: TI (M.Map TypeIndex Pos)
unifyVarsInEnvs = do
  venv <- TI $ asks varEnv
  tenv <- TI $ asks tyEnv
  vtys <- mapM applyCurrentSubst $ M.elems venv
  ttys <- mapM applyCurrentSubst $ M.elems tenv
  return $ M.unionWith choosePos (unifyVars vtys) (unifyVars ttys)

-- Get the named type vars that occur as keys in the current type name
-- environment.
namedVarDefinitions :: TI (S.Set Name)
namedVarDefinitions = do
   env <- TI $ asks tyEnv
   return $ M.keysSet env

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

-- Get all the bindings in a pattern.
patternBindings :: Pattern -> [(Located Name, Maybe Type)]
patternBindings pat =
  case pat of
    PWild _ _mt -> []
    PVar _ x mt -> [(x, mt)]
    PTuple _ ps -> concatMap patternBindings ps

-- }}}


------------------------------------------------------------
-- Unification {{{

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

-- We've found a substitution for unification var i.
--
-- Create the substitution, but first check that this doesn't result
-- in an invalid type.
--
-- Does not handle the case where t _is_ TyUnifyVar i; the caller
-- handles that.
--
-- XXX: we can resolve TyUnifyVar i to TyUnifyVar j here, which is
-- fine as far as it goes but there doesn't seem to be any logic to
-- prohibit also resolving TyUnifyVar j to TyUnifyVar i and creating
-- cycles.
resolveUnificationVar :: Pos -> TypeIndex -> Type -> Either FailMGU Subst
resolveUnificationVar pos i t =
  case M.lookup i $ unifyVars t of
     Just otherpos ->
       -- FIXME/XXX: this error message is better than the one that was here before
       -- but still lacks a certain something
       failMGU' $ "Occurs check failure: the type at " ++ show otherpos ++
                  " appears within the type at " ++ show pos
     Nothing ->
       return (singletonSubst i t)

-- Guts of unification.
--
-- "mgu" stands for "most general unifier".
--
-- Given two types, produce either a failure report or a substitution
-- (to add to the cumulative substitution we build up) that makes them
-- the same.
mgu :: Type -> Type -> Either FailMGU Subst
mgu t1 t2 = case (t1, t2) of

  (TyUnifyVar _ i, TyUnifyVar _ j) | i == j ->
      -- same unification var, nothing to do
      return emptySubst

  (TyUnifyVar pos i, _) ->
      -- one side is a unification var, resolve it
      resolveUnificationVar pos i t2

  (_, TyUnifyVar pos i) ->
      -- one side is a unification var, resolve it
      resolveUnificationVar pos i t1

  (TyRecord _ ts1, TyRecord _ ts2)
    | M.keys ts1 /= M.keys ts2 ->
      -- records with different keys
      failMGU "Record field names mismatch." t1 t2

    | otherwise ->
      -- records with the same field names, try unifying the field types
      case mgus (M.elems ts1) (M.elems ts2) of
        Right result -> Right result
        Left msgs -> Left $ failMGUAdd msgs t1 t2

  (TyCon _ tc1 ts1, TyCon _ tc2 ts2)
    | tc1 == tc2 ->
      -- same type constructor, unify the args
      case mgus ts1 ts2 of
        Right result -> Right result
        Left msgs ->
          -- oops, didn't work. handle functions specially for
          -- nicer error reporting
          case tc1 of
            FunCon -> Left $ failMGUAddFun msgs t1 t2
            _ -> Left $ failMGUAdd msgs t1 t2

    | otherwise ->
      -- Wrong type constructors
      case tc1 of
        FunCon ->
          failMGU ("Term is not a function. (Maybe a function is applied " ++
                   "to too many arguments?)") t1 t2
        _ ->
          failMGU ("Mismatch of type constructors. Expected: " ++ pShow tc1 ++
                   " but got " ++ pShow tc2) t1 t2

  (TyVar _ a, TyVar _ b) | a == b ->
      -- Same named variable
      return emptySubst

  (_, _) ->
      -- Did not work
      failMGU "Mismatch of types." t1 t2

-- Run mgu on two lists of types.
mgus :: [Type] -> [Type] -> Either FailMGU Subst
mgus t1s t2s = case (t1s, t2s) of
    ([], []) ->
        return emptySubst
    (t1 : t1s', t2 : t2s') -> do
        -- unify the first types
        s <- mgu t1 t2
        -- apply that substitution and then recurse
        s' <- mgus (map (appSubst s) t1s') (map (appSubst s) t2s')
        return (mergeSubst s' s)
    (_, _) ->
      -- XXX this is no good, it will always print one of the lengths as 0!
      -- (also, note that this is only reachable for type constructor args
      -- and not function args)
      --
      -- dholland 20250106: I believe this is currently unreachable.
      -- mgus is called from two places above (record fields and type
      -- constructor arguments); the record fields case always passes
      -- lists of the same length. The situation with type constructor
      -- arguments is murkier. However, there are only a handful of
      -- builtin types whose constructors take arguments at all:
      -- tuples, lists, functions, and monads/contexts/blocks. The
      -- parser special-cases the syntax for all of these, so that you
      -- apparently can't produce partially applied instances for
      -- any. (And for tuples, the arity is part of the constructor,
      -- so tuples of different arity won't get as far as trying to
      -- unify the arguments.)
      failMGU' $ "Wrong number of arguments. Expected " ++ show (length t1s) ++
                 " but got " ++ show (length t2s)

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
  t1' <- applyCurrentSubst =<< resolveCurrentTypedefs t1
  t2' <- applyCurrentSubst =<< resolveCurrentTypedefs t2
  case mgu t1' t2' of
    Right s -> TI $ modify $ \rw -> rw { subst = mergeSubst s $ subst rw }
    Left msgs ->
       recordError pos $ unlines $ firstline : morelines'
       where
         firstline = "Type mismatch."
         morelines = ppFailMGU msgs ++ ["within " ++ show m]
         -- Indent all but the first line by four spaces.
         morelines' = map (\msg -> "    " ++ msg) morelines

-- Check if two types match but don't actually unify them
-- (that is, on success throw away the substitution and on error
-- throw away the complaints)
--
-- This is inelegant, and used for some workaround logic to decide
-- which unifications to attempt to avoid failures on things we don't
-- want to make fatal just yet. It should be removed when no longer
-- needed.
matches :: Type -> Type -> TI Bool
matches t1 t2 = do
  t1' <- applyCurrentSubst =<< resolveCurrentTypedefs t1
  t2' <- applyCurrentSubst =<< resolveCurrentTypedefs t2
  case mgu t1' t2' of
    Right _ -> return True
    Left _ -> return False

-- }}}


------------------------------------------------------------
-- Inspect for free type variables {{{

-- We want to allow declaring polymorphic functions by introducing
-- type variables in the function header (rather than requiring an
-- explicit forall binding), like Haskell does.
--
-- This means that free type variables in a function header (but not
-- elsewhere) should be accepted, collected, and handed off to
-- generalize for insertion in the resultant type scheme.
--
-- It turns out that because of the way the AST represents functions
-- in let-bindings that this is highly unpleasant to do on the fly
-- while typechecking. So instead extract the free type variables
-- separately.
--
-- A function header comes through like this:
--    Decl _pos <function-name-pattern> Nothing <expr>
--
-- where <expr> is
--    zero or more times, Function _pos <arg-pattern> <expr'>
--    optionally, TSig _pos <expr''> <return-type>
--
-- so we need any free type variables in
--    - <function-name-pattern>
--    - <return-type>
--    - all <arg-pattern>
--
-- On the plus side this will also then work when people write
-- otherwise annoying things like
--    let f (x: a) = \(y: b) -> (a, b)
--
-- We extract the type variables with the position of their
-- initial mention.

-- Get the free type variables found in a Type.
inspectTypeFTVs :: Type -> TI (Map Name Pos)
inspectTypeFTVs ty = case ty of
    TyCon _pos _ctor args -> M.unions <$> mapM inspectTypeFTVs args
    TyRecord _pos fields -> M.unions <$> traverse inspectTypeFTVs fields
    TyUnifyVar _pos _x -> return M.empty
    TyVar pos x -> do
        tyenv <- TI $ asks tyEnv
        case M.lookup x tyenv of
            Nothing -> return $ M.singleton x pos
            Just _ -> return $ M.empty

-- Get the free type variables found in a Maybe Type.
inspectMaybeTypeFTVs :: Maybe Type -> TI (Map Name Pos)
inspectMaybeTypeFTVs mty = case mty of
    Nothing -> return M.empty
    Just ty -> inspectTypeFTVs ty

-- Get the free type variables found in a Pattern.
inspectPatternFTVs :: Pattern -> TI (Map Name Pos)
inspectPatternFTVs pat = case pat of
    PWild _pos mty -> inspectMaybeTypeFTVs mty
    PVar _pos _x mty -> inspectMaybeTypeFTVs mty
    PTuple _pos subpats ->
        M.unions <$> mapM inspectPatternFTVs subpats

-- Get the free type variables found in a chain of Function Exprs.
-- Also return the body expression found on the inside of the chain
-- for possible further analysis.
inspectLambdaFTVs :: Expr -> TI (Expr, Map Name Pos)
inspectLambdaFTVs e0 = case e0 of
    Function _fpos pat e1 -> do
        hereFTVs <- inspectPatternFTVs pat
        (e1', moreFTVs) <- inspectLambdaFTVs e1
        return (e1', M.union hereFTVs moreFTVs)
    _ ->
        return (e0, M.empty)

-- Get the free type variables found in a Decl.
inspectDeclFTVs :: Decl -> TI (Map Name Pos)
inspectDeclFTVs (Decl _dpos pat _mty e0) = do
    nameFTVs <- inspectPatternFTVs pat
    (e1, argFTVs) <- inspectLambdaFTVs e0
    retFTVs <- case e1 of
        TSig _tspos _e2 ty -> inspectTypeFTVs ty
        _ -> return M.empty
    return $ M.unions [nameFTVs, argFTVs, retFTVs]


-- }}}


------------------------------------------------------------
-- Main recursive pass {{{

type OutExpr = Expr
type OutStmt = Stmt

--
-- Expressions
--

-- Take a struct field binding (name and expression) and return the
-- updated binding as well as the member entry for the enclosing
-- struct type.
inferField :: LName -> (Name, Expr) -> TI ((Name, OutExpr), (Name, Type))
inferField m (n,e) = do
  (e',t) <- inferExpr (m,e)
  return ((n,e'),(n,t))

-- wrap the action m with a type for x
withVar :: Located Name -> Schema -> TI a -> TI a
withVar x s m =
  TI $ local (\ro -> ro { varEnv = M.insert x s $ varEnv ro }) $ unTI m

-- wrap the action m with types for a list of vars
withVars :: [(Located Name, Schema)] -> TI a -> TI a
withVars bindings m = foldr (uncurry withVar) m bindings

-- wrap the action m with types for all the vars in a pattern
--
-- (note that the pattern should have already been processed so it
-- contains types; hence the irrefutable Just t)
withPattern :: Pattern -> TI a -> TI a
withPattern pat m = withVars bindings m
  where bindings = [ (x, tMono t) | (x, Just t) <- patternBindings pat ]

-- wrap the action m with types for all the vars in a pattern, using
-- the passed-in schema to produce the types and ignoring the types
-- already loaded into the pattern.
--
-- XXX: is that what we want? should probably assert that the schema
-- matches the types in the pattern, unless the pattern hasn't already
-- been checked yet, and that seems like it would be a bug.
--
-- Note that if the pattern is a tuple and the schema is not a tuple
-- type, we do nothing. Presumably in this case a type error has
-- already been generated and we don't need another one? But it would
-- probably be a good idea to check up on that. XXX
withPatternSchema :: Pattern -> Schema -> TI a -> TI a
withPatternSchema pat s@(Forall vs t) m =
  case pat of
    PWild _ _ -> m
    PVar _ x _ -> withVar x s m
    PTuple _ ps ->
      case t of
        TyCon _pos (TupleCon _) ts -> foldr ($) m
          [ withPatternSchema p (Forall vs t') | (p, t') <- zip ps ts ]
        _ -> m

-- wrap the action m with types for the vars in a declaration.
--
-- Do nothing if there's no type schema in this declaration yet.
withDecl :: Decl -> TI a -> TI a
withDecl (Decl _ _ Nothing _) m = m
withDecl (Decl _ p (Just s) _) m = withPatternSchema p s m

-- wrap the action m with types for the vars in a declgroup.
withDeclGroup :: DeclGroup -> TI a -> TI a
withDeclGroup (NonRecursive d) m = withDecl d m
withDeclGroup (Recursive ds) m = foldr withDecl m ds

-- wrap the action m with some abstract type variables.
withAbstractTyVars :: Map Name Pos -> TI a -> TI a
withAbstractTyVars vars m = do
    let insertOne x _pos tyenv = M.insert x AbstractType tyenv
        insertAll tyenv = M.foldrWithKey insertOne tyenv vars
    TI $ local (\ro -> ro { tyEnv = insertAll $ tyEnv ro }) $ unTI m

--
-- Infer the type for an expression.
--
-- The LName is the context name passed to unify, which isn't generally
-- useful and should probably be removed.
--
inferExpr :: (LName, Expr) -> TI (OutExpr,Type)
inferExpr (ln, expr) = case expr of
  Bool pos b    -> return (Bool pos b, tBool (PosInferred InfTerm pos))
  String pos s  -> return (String pos s, tString (PosInferred InfTerm pos))
  Int pos i     -> return (Int pos i, tInt (PosInferred InfTerm pos))
  Code s        -> return (Code s, tTerm (PosInferred InfTerm $ getPos s))
  CType s       -> return (CType s, tType (PosInferred InfTerm $ getPos s))

  Array pos [] ->
    do a <- getFreshTyVar pos
       return (Array pos [], tArray (PosInferred InfTerm pos) a)

  Array pos (e:es) ->
    do (e',t) <- inferExpr (ln, e)
       es' <- mapM (flip (checkExpr ln) t) es
       return (Array pos (e':es'), tArray (PosInferred InfTerm pos) t)

  Block pos bs ->
    do ctx <- getFreshTyVar pos
       (bs',t') <- inferStmts ln pos ctx bs
       return (Block pos bs', tBlock (PosInferred InfTerm pos) ctx t')

  Tuple pos es ->
    do (es',ts) <- unzip `fmap` mapM (inferExpr . (ln,)) es
       return (Tuple pos es', tTuple (PosInferred InfTerm pos) ts)

  Record pos fs ->
    do (nes',nts) <- unzip `fmap` mapM (inferField ln) (M.toList fs)
       let ty = TyRecord (PosInferred InfTerm pos) $ M.fromList nts
       return (Record pos (M.fromList nes'), ty)

  -- XXX this is currently unreachable because there's no concrete
  -- syntax for it; the parser will never produce it.
  Index pos ar ix ->
    do (ar',at) <- inferExpr (ln,ar)
       ix'      <- checkExpr ln ix (tInt (PosInferred InfContext (getPos ix)))
       t        <- getFreshTyVar (getPos ix')
       unify ln (tArray (PosInferred InfContext (getPos ar')) t) (getPos ar') at
       return (Index pos ar' ix', t)

  Lookup pos e n ->
    do (e1,t) <- inferExpr (ln, e)
       t1 <- applyCurrentSubst =<< resolveCurrentTypedefs t
       elTy <- case t1 of
           TyRecord typos fs
            | Just ty <- M.lookup n fs -> do
               return ty
            | otherwise -> do
               recordError pos $
                   "Record type has no field named " ++ Text.unpack n
               getErrorTyVar typos
           TyUnifyVar _ _ -> do
               recordError pos $
                   "Cannot infer a record type for field " ++
                   Text.unpack n ++ "; please use a type annotation"
               getErrorTyVar pos
           _ -> do
               recordError pos $
                   "Record lookup on non-record value of type " ++ pShow t1
               getErrorTyVar pos
       return (Lookup pos e1 n, elTy)

  TLookup pos e i ->
    do (e1,t) <- inferExpr (ln,e)
       t1 <- applyCurrentSubst =<< resolveCurrentTypedefs t
       elTy <- case t1 of
           TyCon typos (TupleCon n) tys
            | i < n ->
               return (tys !! fromIntegral i)
            | otherwise -> do
               recordError pos $
                   "Tuple index " ++ show i ++ " out of bounds; limit is " ++
                   show n
               getErrorTyVar typos
           TyUnifyVar _ _ -> do
               recordError pos $
                   "Cannot infer tuple arity for lookup of element " ++
                   show i ++ "; please use a type annotation"
               getErrorTyVar pos
           _ -> do
               recordError pos $ 
                   "Tuple lookup on non-tuple value of type " ++ pShow t1
               getErrorTyVar pos
       return (TLookup pos e1 i, elTy)

  Var x ->
    do env <- TI $ asks varEnv
       case M.lookup x env of
         Nothing -> do
           recordError (getPos x) $ unlines
             [ "Unbound variable: " ++ show x
             , "Note that some built-in commands are available only after running"
             , "either `enable_deprecated` or `enable_experimental`."
             ]
           t <- getFreshTyVar (getPos x)
           return (Var x, t)
         Just (Forall as t) -> do
           -- get a fresh tyvar for each quantifier binding, convert
           -- to a name -> ty map, and instantiate with the fresh tyvars
           let once (apos, a) = do
                 at <- getFreshTyVar apos
                 return (a, ConcreteType at)
           substs <- mapM once as
           let t' = instantiate (M.fromList substs) t
           return (Var x, t')

  Function pos pat body ->
    do (pt, pat') <- inferPattern pat
       (body', t) <- withPattern pat' $ inferExpr (ln, body)
       return (Function pos pat' body', tFun (PosInferred InfContext (getPos body)) pt t)

  Application pos f arg ->
    do argtype <- getFreshTyVar pos
       rettype <- getFreshTyVar pos
       let ftype = tFun (PosInferred InfContext $ getPos f) argtype rettype
       -- Check f' first so that we complain about the arg (not the
       -- function) if they don't match. This is what everyone expects
       -- and doing it the other way is surprisingly confusing.
       f' <- checkExpr ln f ftype
       arg' <- checkExpr ln arg argtype
       return (Application pos f' arg', rettype)

  Let pos dg body ->
    do dg' <- inferDeclGroup dg
       (body', t) <- withDeclGroup dg' (inferExpr (ln, body))
       return (Let pos dg' body', t)

  TSig _pos e t ->
    do t' <- checkType kindStar t
       (e',t'') <- inferExpr (ln,e)
       unify ln t' (getPos e') t''
       return (e',t'')

  IfThenElse pos e1 e2 e3 ->
    do e1' <- checkExpr ln e1 (tBool (PosInferred InfContext $ getPos e1))
       (e2', t) <- inferExpr (ln, e2)
       e3' <- checkExpr ln e3 t
       return (IfThenElse pos e1' e2' e3', t)

--
-- Check the type of an expr, by inferring and then unifying the
-- result.
--
checkExpr :: LName -> Expr -> Type -> TI OutExpr
checkExpr m e t = do
  (e',t') <- inferExpr (m,e)
  unify m t (getPos e') t'
  return e'

--
-- patterns
--

-- Infer types for a pattern, producing fresh type variables as needed.
--
-- There may already be types in the pattern if there were explicit
-- type annotations in the input; if so don't throw them away.
inferPattern :: Pattern -> TI (Type, Pattern)
inferPattern pat =
  let resolveType pos mt = case mt of
        Nothing -> getFreshTyVar pos
        Just t -> checkType kindStar t
  in
  case pat of
    PWild pos mt ->
      do t <- resolveType pos mt
         return (t, PWild pos (Just t))
    PVar pos x mt ->
      do t <- resolveType pos mt
         return (t, PVar pos x (Just t))
    PTuple pos ps ->
      do (ts, ps') <- unzip <$> mapM inferPattern ps
         return (tTuple (PosInferred InfTerm pos) ts, PTuple pos ps')

-- Check the type of a pattern, by inferring and then unifying the
-- result.
checkPattern :: LName -> Type -> Pattern -> TI Pattern
checkPattern ln t pat =
  do (pt, pat') <- inferPattern pat
     unify ln t (getPos pat) pt
     return pat'

--
-- statements
--

-- wrap m with a typedef binding
withTypedef :: LName -> Type -> TI a -> TI a
withTypedef n t m =
  TI $
  local
    (\ro ->
      let t' = instantiate (tyEnv ro) t
      in  ro { tyEnv = M.insert (getVal n) (ConcreteType t') $ tyEnv ro })
    $ unTI m

-- Check if a statement is an allowable one for the end of a do-block.
-- The last thing in a do-block should be an expression, which manifests
-- as a bind-statement of the form _ <- e.
legalEndOfBlock :: Stmt -> Bool
legalEndOfBlock s = case s of
    StmtBind _spos (PWild _patpos _mt) _e -> True
    _ -> False

-- break a monadic type down into its monad and value types, if it is one
--
--    monadType (TopLevel Int) gives Just (TopLevel, Int)
--    monadType Int gives Nothing
--
monadType  :: Type -> Maybe (Type, Type)
monadType ty = case ty of
  TyCon _ BlockCon [ctx@(TyCon _ (ContextCon _) []), valty] ->
      Just (ctx, valty)
  -- We don't currently ever generate this type, but be future-proof
  TyCon pos (ContextCon ctx) [valty] ->
      Just (TyCon pos (ContextCon ctx) [], valty)
  _ ->
      Nothing

-- wrap an expression in "return"
wrapReturn :: Expr -> Expr
wrapReturn e =
   let ePos = getPos e
       retPos = PosInternal "<implicitly inserted return>"
       ret = Var $ Located "return" "return" retPos 
   in
   Application ePos ret e

-- type inference for a single statement
--
-- the boolean is whether we're at the syntactic top level, which is used
-- for workaround logic for issue #2162
--
-- the passed-in position should be the position associated with the monad type
-- the first type argument (ctx) is the monad type for any binds that occur
--
-- returns a wrapper for checking subsequent statements as well as
-- an updated statement and a type.
inferStmt :: LName -> Bool -> Pos -> Type -> Stmt -> TI (TI a -> TI a, Stmt, Type)
inferStmt ln atSyntacticTopLevel blockpos ctx s =
    case s of
        StmtBind spos pat e -> do
            (pty, pat') <- inferPattern pat
            -- The expression should be of monad type. The
            -- straightforward way to proceed here is to unify both
            -- the monad type (ctx) and the result type expected by
            -- the pattern (pty), like this:
            --    e' <- checkExpr ln e (tBlock blockpos ctx pty)
            --
            -- However, historically when at the syntactic top level
            -- (only), the monad type was left off, meaning that
            -- various incorrect forms were silently accepted. Fixing
            -- this in Dec 2024 triggered a lot of fallout, so for the
            -- time being we want to check for, warn about, and allow
            -- the following cases. (Again, only when at the syntactic
            -- top level. Which is not when in the TopLevel monad.)
            --    x <- e for non-monadic e
            --    x <- e for e in the wrong monad
            --
            -- These should be made errors again at some point, but
            -- definitely no earlier than the _second_ release after
            -- December 2024, as the first such release should include
            -- the warning behavior. Probably the explicit messages
            -- should then in turn not be removed for at least one
            -- further release. See #2167 and #2162.
            --
            -- To accomplish this, call inferExpr to get a type for
            -- the expression, and examine it. If the special cases
            -- apply, issue special-case warnings with explanations,
            -- unify the type with only the pattern type, and patch up
            -- the expression by wrapping it in "return".  (The latter
            -- will restore the old behavior for both cases, so we
            -- don't need to also gunk up the interpreter to handle
            -- this problem.)
            --
            -- If the special cases don't apply, unify the result type
            -- with the complete type.
            (e', ty) <- inferExpr (ln, e)
            ty' <- applyCurrentSubst =<< resolveCurrentTypedefs ty

            -- The correct, restricted case
            let restrictToCorrect = do
                  -- unify the type of e with the expected monad and
                  -- pattern types
                  unify ln (tBlock blockpos ctx pty) (getPos e') ty
                  return e'

            -- The special case for non-monadic values
            let allowNonMonadic = do
                  recordWarning spos $ "Monadic bind of non-monadic value; " ++
                                       "rewrite as let-binding or use return"
                  recordWarning spos $ "This will become an error in a " ++
                                       "future release of SAW"
                  unify ln pty (getPos e') ty
                  -- Wrap the expression in "return" to correct the type
                  return $ wrapReturn e'

            -- The special case for the wrong monad
            let allowWrongMonad ctx' valty' = do
                  recordWarning spos $ "Monadic bind with the wrong monad; " ++
                                       "found " ++ pShow ctx' ++
                                       " but expected " ++ pShow ctx
                  recordWarning spos $ "This creates the action but does " ++
                                       "not execute it; if you meant to do " ++
                                       "that, prefix the " ++
                                       "expression with return"
                  recordWarning spos $ "This will become an error in a " ++
                                       "future release of SAW"

                  -- The historic behavior is that the pattern gets bound
                  -- to a value of type m t instead of type t. This means:
                  --    - we should unify pty, which is the type of the
                  --      pattern, with m t, which is tBlock ctx' valty'
                  --      (rather than tBlock ctx valty', which is the
                  --      type we should be getting)
                  --    - this will fail if the pattern includes a type
                  --      signature with a non-monad type, but that's ok
                  --      because that case also fails in old SAW
                  --    - we do _not_ need to update pty before returning
                  --      it out of inferStmt
                  --    - we _do_ need to wrap the expression in "return"
                  --      so that the ultimate results are well-typed and
                  --      happen in the TopLevel monad
                  unify ln pty (getPos e') (tBlock spos ctx' valty')

                  -- Wrap the expression in "return" to produce an
                  -- expression of type TopLevel (m t).
                  return $ wrapReturn e'

            -- Figure out which case applies.
            e'' <-
                if not atSyntacticTopLevel then
                    restrictToCorrect
                else do
                    ok <- matches (tBlock blockpos ctx pty) ty
                    if ok then
                        restrictToCorrect
                    else
                        case monadType ty' of
                            Just (ctx', valty') ->
                               -- Allow it only for _ and a single var.
                               -- Binding elements of a tuple this way
                               -- failed typecheck in the old saw and
                               -- doesn't need to be allowed now.
                               case pat of
                                   PTuple _ _ -> restrictToCorrect
                                   _ -> allowWrongMonad ctx' valty'
                            Nothing ->
                               -- allow it only if actually binding something
                               -- (just proclaiming a value by itself is not a
                               -- case we need to worry about)
                               case pat of
                                   PWild _ _ -> restrictToCorrect
                                   _ -> allowNonMonadic

            let s' = StmtBind spos pat' e''
            let wrapper = withPattern pat'
            return (wrapper, s', pty)
        StmtLet spos dg -> do
            dg' <- inferDeclGroup dg
            let s' = StmtLet spos dg'
            let wrapper = withDeclGroup dg'
            return (wrapper, s', tUnit $ PosInferred InfTerm spos)
        StmtCode spos _ ->
            return (id, s, tUnit $ PosInferred InfTerm spos)
        StmtImport spos _ ->
            return (id, s, tUnit $ PosInferred InfTerm spos)
        StmtTypedef spos name ty -> do
            ty' <- checkType kindStar ty
            let s' = StmtTypedef spos name ty'
            let wrapper = withTypedef name ty'
            return (wrapper, s', tUnit $ PosInferred InfTerm spos)

-- the passed-in position should be the position for the whole statement block
-- the first type argument (ctx) is the monad type for the block
inferStmts :: LName -> Pos -> Type -> [Stmt] -> TI ([OutStmt], Type)
inferStmts ln blockpos ctx stmts = case stmts of
    [] -> do
        recordError blockpos ("do block must include at least one " ++
                              "expression at " ++ show ln)
        t <- getErrorTyVar blockpos
        return ([], t)

    s : more -> do
        let atSyntacticTopLevel = False
        (wrapper, s', t) <- inferStmt ln atSyntacticTopLevel blockpos ctx s
        case more of
            [] ->
                if legalEndOfBlock s then
                    return ([s'], t)
                else do
                    recordError blockpos ("do block must end with " ++
                                          "expression at " ++ show ln)
                    t' <- getErrorTyVar blockpos
                    -- XXX this has been throwing away s' but probably shouldn't
                    return ([], t')
            _ : _ -> do
               (more', t') <- wrapper $ inferStmts ln blockpos ctx more
               return (s' : more', t')

-- Wrapper around inferStmt suitable for checking one statement at a
-- time. This is temporary scaffolding for the interpreter while
-- fixing it. (Currently the interpreter typechecks one statement at a
-- time when executing, even when not at the repl, and this involves
-- assorted messiness and technical debt. Eventually we'll get it into
-- a state where we can always just typecheck immediately after
-- parsing (including incrementally from the repl) but we're some
-- distance from that. In the meantime the first step is to get it to
-- typecheck one statement at a time without special-casing any of
-- them, and this is how it does that.
--
-- Run inferStmt and then apply the current substitution before
-- returning the updated statement. Ignore the wrapper returned for
-- typechecking subsequent statements; the interpreter has its own
-- (misbegotten) logic for handling that in its own way. (Which should
-- be removed, but we need to get rid of these wrappers here first;
-- any sane incremental typechecking interface requires updating the
-- environment for sequential declarations, not pretending that
-- subsequent statements in a block are nested inside prior ones.)
inferSingleStmt :: LName -> Pos -> Type -> Stmt -> TI Stmt
inferSingleStmt ln pos ctx s = do
  -- currently we are always at the syntactic top level here because
  -- that's how the interpreter works
  let atSyntacticTopLevel = True
  (_wrapper, s', _ty') <- inferStmt ln atSyntacticTopLevel pos ctx s
  s'' <- applyCurrentSubst s'
  return s''

--
-- decls
--

-- Create a type schema for a list of mutually referential
-- declarations out of their free vars.
--
-- (This creates names for any remaining unification vars, so
-- potentially updates the expression.)
--
-- The "foralls" argument is a set of tyvars that were mentioned
-- explicitly and should be forall-bound.
generalize :: Map Name Pos -> [OutExpr] -> [Type] -> TI [(OutExpr,Schema)]
generalize foralls es0 ts0 = do
     -- first, substitute away any resolved unification variables
     -- in both the expressions and types.
     es <- applyCurrentSubst es0
     ts <- applyCurrentSubst ts0

     -- Extract lists of any unification vars and named type vars that
     -- still appear.
     let is0 = unifyVars ts
     let bs0 = namedVars ts

     -- Drop any unification vars and named type vars that we
     -- shouldn't forall-bind.
     --
     -- For unification vars, any whose scope reaches beyond the
     -- current declaration should be left alone; they should only be
     -- bound when they eventually move out of scope. Get these by
     -- examining the types used in the right-hand sides of both the
     -- variable environment and the type environment.
     --
     -- For named vars, exclude any that appear that appear as keys
     -- (on the left-hand side) of the type environment. Those are
     -- already defined.
     --
     -- The only other named variables involved should be the set we
     -- explicitly intend to be forall-bound as passed in. Insert
     -- those, and favor their positions.
     --
     -- It would be handy for scaling if we didn't have to examine
     -- the entire variable environment (on the grounds that there
     -- should be no loose unification vars at the top level where
     -- most definitions will come from) but (a) we don't have the
     -- structure to support that and (b) it is not absolutely clear
     -- that there isn't a way to get such loose unification vars,
     -- in which case we'd have to do something about it.
     --
     -- This code also used to exclude named vars used on the
     -- right-hand side of the variable environment; this was to allow
     -- the use of otherwise undefined type names in the primitives
     -- table. There is no longer any need for such hackery, and
     -- undefined type names are not allowed to appear in the variable
     -- environment.
     --
     -- FUTURE: we end up replacing the user's forall-bound names with
     -- generated names, and I'm not sure why. It seems like it
     -- shouldn't be possible the way the code is structured. But the
     -- type signatures are coming out correct (which they wouldn't if
     -- something were seriously wrong) and we aren't inappropriately
     -- unifying these vars with each other or with other things, so
     -- I'm not going to stress over it right now.

     envUnifyVars <- unifyVarsInEnvs
     knownNamedVars <- namedVarDefinitions
     let is1 = is0 M.\\ envUnifyVars
     let bs1 = M.union foralls $ M.withoutKeys bs0 knownNamedVars

     -- convert to lists
     let is2 = M.toList is1
     let bs2 = M.toList bs1

     -- if the position is "fresh" turn it into "inferred from term"
     let adjustPos pos = case pos of
           PosInferred InfFresh pos' -> PosInferred InfTerm pos'
           _ -> pos

     -- generate names for the unification vars
     let is3 = [ (i, adjustPos pos, "a." <> Text.pack (show i)) | (i, pos) <- is2 ]

     -- build a substitution
     let s = substFromList [ (i, TyVar pos n) | (i, pos, n) <- is3 ]

     -- get the names for the Forall
     let inames = [ (pos, n) | (_i, pos, n) <- is3 ]
     let bnames = [ (pos, x) | (x, pos) <- bs2 ]

     let mk e t = (appSubst s e, Forall (inames ++ bnames) (appSubst s t))

     return $ zipWith mk es ts

-- Type inference for a declaration.
--
-- Note that the type schema slot in Decl is always Nothing as we get
-- it from the parser; if there's an explicit type annotation on the
-- declaration that shows up as a type signature in the expression.
inferDecl :: Decl -> TI Decl
inferDecl d@(Decl pos pat _ e) = do
  let n = patternLName pat
  foralls <- inspectDeclFTVs d
  withAbstractTyVars foralls $ do
    (e',t) <- inferExpr (n, e)
    pat' <- checkPattern n t pat
    ~[(e1,s)] <- generalize foralls [e'] [t]
    return (Decl pos pat' (Just s) e1)

-- Type inference for a system of mutually recursive declarations.
--
-- Note that the type schema slot in the Decls is always Nothing as we
-- get them from the parser; if there's an explicit type annotation on
-- some or all of the declarations those shows up as type signatures
-- in the expressions.
inferRecDecls :: [Decl] -> TI [Decl]
inferRecDecls ds =
  do let pats = map dPat ds
         firstPat =
           case pats of
             p:_ -> p
             [] -> panic
                     "inferRecDecls"
                     ["Empty list of declarations in recursive group"]
     foralls <- M.unions <$> mapM inspectDeclFTVs ds
     withAbstractTyVars foralls $ do
       (_ts, pats') <- unzip <$> mapM inferPattern pats
       (es, ts) <- fmap unzip
                   $ flip (foldr withPattern) pats'
                   $ sequence [ inferExpr (patternLName p, e)
                              | Decl _pos p _ e <- ds
                              ]

       -- pats' has already been checked once, which will have inserted
       -- unification vars for any missing types. Running it through
       -- again will have no further effect, so we can ignore the
       -- theoretically-updated-again patterns returned by checkPattern.
       sequence_ $ zipWith (checkPattern (patternLName firstPat)) ts pats'
       ess <- generalize foralls es ts
       return [ Decl pos p (Just s) e1
              | (pos, p, (e1, s)) <- zip3 (map getPos ds) pats' ess
              ]

-- Type inference for a decl group.
inferDeclGroup :: DeclGroup -> TI DeclGroup
inferDeclGroup (NonRecursive d) = do
  d' <- inferDecl d
  return (NonRecursive d')

inferDeclGroup (Recursive ds) = do
  ds' <- inferRecDecls ds
  return (Recursive ds')

--
-- types
--

-- Look up a type constructor (in our fixed environment of hardcoded
-- types) and return its params as a list of kinds.
lookupTyCon :: TyCon -> [Kind]
lookupTyCon tycon = case tycon of
  TupleCon n -> genericTake n (repeat kindStar)
  ArrayCon -> [kindStar]
  FunCon -> [kindStar, kindStar]
  StringCon -> []
  TermCon -> []
  TypeCon -> []
  BoolCon -> []
  IntCon -> []
  BlockCon -> [kindStar, kindStar]
  AIGCon -> []
  CFGCon -> []
  JVMSpecCon -> []
  LLVMSpecCon -> []
  MIRSpecCon -> []
  ContextCon _ctx ->
    -- XXX: while BlockCon exists, ContextCon has kind * and you
    -- have to use BlockCon to paste a result type to a ContextCon.
    -- (BlockCon should be removed. Then ContextCon has kind * -> *
    -- like you'd expect.)
    []

-- Check a type for validity and also for having the
-- correct kinding.
checkType :: Kind -> Type -> TI Type
checkType kind ty = case ty of
  TyCon pos tycon args -> do
      -- First, look up the constructor.
      let params = lookupTyCon tycon
      let nparams = length params
          nargs = length args
          argsleft = kindNumArgs kind

      -- XXX: the failures are all currently unreachable, because the
      -- parser does not permit writing mis-kinded types. This should
      -- probably be changed, both for ergonomic reasons (messages
      -- about wrong type arguments are better than syntax errors) and
      -- also because all the special cases in the parser are ugly.

      if nargs > nparams then do
          -- XXX special case for BlockCon (remove along with BlockCon)
          case (tycon, args) of
              (BlockCon, arg : _) ->
                  recordError pos ("Too many type arguments for type " ++
                                   "constructor " ++ pShow arg ++
                                   "; found " ++ show (nargs - 1) ++
                                   " but expected only " ++ show (nparams - 1))
              (_, _) ->
                  recordError pos ("Too many type arguments for type " ++
                                   "constructor " ++ pShow tycon ++
                                   "; found " ++ show nargs ++
                                   " but expected only " ++ show nparams)
          getErrorTyVar pos
      else if nargs + argsleft /= nparams then do
          recordError pos ("Kind mismatch: expected " ++ pShow kind ++
                           " but found " ++ (pShow $ Kind (nparams - nargs)))
          getErrorTyVar pos
      else do
          -- note that this will ignore the extra params, and return
          -- a list of the same length as the args given
          args' <- zipWithM checkType params args
          return $ TyCon pos tycon args'

  TyRecord pos fields -> do
      -- XXX as with TyCon the failure is currently unreachable
      -- because the parser can't be made to produce mis-kinded types.
      if kind /= kindStar then do
          recordError pos ("Kind mismatch: expected " ++ pShow kind ++
                           " but found " ++ pShow kindStar)
          getErrorTyVar pos
      else do
          -- Someone upstream had better have checked for duplicate
          -- field names because we can't once the fields are loaded
          -- into a map. (XXX: someone hasn't)
          fields' <- traverse (checkType kindStar) fields
          return $ TyRecord pos fields'

  TyVar pos x -> do
      tyenv <- TI $ asks tyEnv
      case M.lookup x tyenv of
          Nothing -> do
              recordError pos ("Unbound type variable " ++ Text.unpack x)
              getErrorTyVar pos
          Just _ty' ->
              -- Assume ty' was checked when it was entered.
              -- (If we entered it that's true, if it was in the
              -- initial environment we were given that depends on the
              -- interpreter not doing unfortunate things. This isn't
              -- currently seeming like a very good bet.)
              --
              -- For now at least we require typedefs to be kind *
              -- (they can't have parameters and the expansions are thus
              -- restricted) so just fail if we use one in a context
              -- expecting something else.
              --
              -- The same holds for abstract types, so we don't need
              -- separate cases.
              if kind /= kindStar then do
                  recordError pos ("Kind mismatch: expected " ++ pShow kind ++
                                   " but found " ++ pShow kindStar)
                  getErrorTyVar pos
              else
                  -- We do _not_ want to expand typedefs when checking,
                  -- so return the original TyVar.
                  return ty

  TyUnifyVar _pos _ix ->
      -- for now at least we don't track the kinds of unification vars
      -- (types of mismatch kinds can't be the same types, so they
      -- won't ever unify, so the possible mischief is limited) and all
      -- possible unification var numbers are well formed, so we don't
      -- need to do anything.
      return ty


-- }}}


------------------------------------------------------------
-- External interface {{{

-- Some short names for use in the signatures below
type MsgList = [(Pos, String)]
type Result a = (Either MsgList a, MsgList)

-- Run the TI monad.
--
-- Note that the error and warning lists accumulate in reverse order
-- (later messages are consed onto the head of the list) so we
-- reverse on the way out.
runTIWithEnv :: VarEnv -> TyEnv -> TI a -> (a, Subst, MsgList, MsgList)
runTIWithEnv env tenv m = (a, subst rw, reverse $ errors rw, reverse $ warnings rw)
  where
  m' = runReaderT (unTI m) (RO env tenv)
  (a,rw) = runState m' emptyRW

-- Run the TI monad and interpret/collect the results
-- (failure if any errors were produced)
evalTIWithEnv :: VarEnv -> TyEnv -> TI a -> Result a
evalTIWithEnv env tenv m =
  case runTIWithEnv env tenv m of
    (res, _, [], warns) -> (Right res, warns)
    (_, _, errs, warns) -> (Left errs, warns)

-- | Check a single statement. (This is an external interface.)
--
-- The first two arguments are the starting variable and typedef
-- environments to use.
--
-- The third is a current position, and the fourth is the
-- context/monad type associated with the execution.
checkStmt :: VarEnv -> TyEnv -> Context -> Stmt -> Result Stmt
checkStmt env tenv ctx stmt =
  -- XXX: we shouldn't need this position here.
  -- The position is used for the following things:
  --
  --    - to create ln, which is used as part of the error printing
  --      scheme, but is no longer particularly useful after recent
  --      improvements (especially here where it contains no real
  --      information) and should be removed;
  --
  --    - to be the position associated with the monad context, which
  --      in a tidy world should just be PosRepl (as in, the only
  --      time we should be typechecking a single statement is when
  --      it was just typed interactively, and which monad we're in
  --      is a direct property of that context) but this is not
  --      currently true and will require a good bit of interpreter
  --      cleanup to make it true;
  --
  --    - to pass to inferStmt, which also uses it as part of the
  --      position associated with the monad context. (This part is a
  --      result of BlockCon existing and can go away when BlockCon is
  --      removed.)
  --
  -- XXX: using the position of the statement as the position
  -- associated with the monad context is not correct (or at least,
  -- will be confusing) and we should figure something else out if the
  -- interpreter cleanup doesn't come through soon. Note that
  -- currently we come through here only for syntactically top-level
  -- statements in the interpreter; these are TopLevel except when in
  -- the ProofScript repl. So perhaps we should use PosRepl when in
  -- ProofScript, and then either PosRepl or PosBuiltin for TopLevel?
  -- But we don't have a good way of knowing here whether we're
  -- actually in the repl.
  let pos = getPos stmt
      ln = case ctx of
          TopLevel -> Located "<toplevel>" "<toplevel>" pos
          ProofScript -> Located "<proofscript>" "<proofscript>" pos
          _ -> panic "checkStmt" ["Invalid monad context " ++ pShow ctx]
      ctxtype = TyCon pos (ContextCon ctx) []
  in
  evalTIWithEnv env tenv (inferSingleStmt ln pos ctxtype stmt)

-- | Check a single declaration. (This is an external interface.)
--
-- The first two arguments are the starting variable and typedef
-- environments to use.
checkDecl :: VarEnv -> TyEnv -> Decl -> Result Decl
checkDecl env tenv decl =
  evalTIWithEnv env tenv (inferDecl decl)

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
