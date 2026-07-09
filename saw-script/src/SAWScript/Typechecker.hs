{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
-- See Note [-Wincomplete-uni-patterns and irrefutable patterns]
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

{- |
Module      : SAWScript.Typechecker
Description : SAWScript type checking.
License     : BSD3
Maintainer  : saw@galois.com
Stability   : provisional

This module contains the typechecker for SAWScript.
-}

module SAWScript.Typechecker
    ( checkDecl
    , checkStmt
    , typesMatch
    , checkSchema
    , checkSchemaPattern
    ) where

import Control.Monad (when, zipWithM, foldM, zipWithM_)
import Control.Monad.Reader (MonadReader(..), ReaderT(..), asks)
import Control.Monad.State (MonadState(..), StateT, gets, modify, runState)
import Control.Monad.Identity (Identity)
import qualified Data.Text as Text
import Data.Text (Text)
import Data.List (genericTake, genericLength)
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)

import qualified Prettyprinter as PP
import Prettyprinter ((<+>))

import qualified SAWSupport.Pretty as PPS
import qualified SAWSupport.ScopedMap as ScopedMap
import SAWSupport.ScopedMap (ScopedMap)

-- For the moment, import bits of Position that are effectively part
-- of the AST unqualified, and qualify the rest. Revisit this once we
-- get around to tidying up the position types and therefore having
-- less junk in the Position module.
import qualified SAWCentral.Position as Pos
import SAWCentral.Position (Inference(..), Pos(..))
import SAWCentral.AST
import qualified SAWCentral.ASTUtil as Util

import SAWScript.Panic (panic)


-- short names for the environment types we use
type VarEnv = ScopedMap Name (Pos, PrimitiveLifecycle, Rebindable, Schema)
type TyEnv = ScopedMap Name (PrimitiveLifecycle, NamedType)


------------------------------------------------------------
-- Support bits

-- | Like zipWithM_ on two lists, but on maps by aligning keys.
--   This could also perhaps be called intersectionWithM, but
--   since it doesn't actually compute a resultant map that seems
--   misleading.
zipByKeyWithM_ :: (Ord k, Monad m) =>
      (a -> b -> m ()) -> Map k a -> Map k b ->
      m ()
zipByKeyWithM_ f xs ys =
    let xys = Map.intersectionWith (\x y -> (x, y)) xs ys in
    mapM_ (\(x, y) -> f x y) (Map.elems xys)

-- | Drop a list of keys from xs.
dropKeys :: Ord k => [k] -> Map k v -> Map k v
dropKeys keys xs =
    foldr Map.delete xs keys


------------------------------------------------------------
-- UnifyVars

--
-- unifyVars is a type-class-polymorphic function for extracting
-- unification vars from a type or type schema. It returns a set of
-- TypeIndex (TypeIndex is just Integer) manifested as a map from
-- those TypeIndexes to their positions/provenance.
--

class UnifyVars t where
    unifyVars :: t -> Map TypeIndex Pos

instance (Ord k, UnifyVars a) => UnifyVars (Map k a) where
    unifyVars = unifyVars . Map.elems

instance (UnifyVars a) => UnifyVars [a] where
    unifyVars = Map.unionsWith Pos.choosePos . map unifyVars

instance (UnifyVars a) => UnifyVars (PrimitiveLifecycle, a) where
    unifyVars (_lc, t) = unifyVars t

instance (UnifyVars a) => UnifyVars (Pos, PrimitiveLifecycle, Rebindable, a) where
    unifyVars (_pos, _lc, _rb, t) = unifyVars t

instance UnifyVars Type where
    unifyVars t = case t of
        TyCon _ _ ts      -> unifyVars ts
        TyFunc _ _ params namedParams ret ->
            let paramsVars = unifyVars params
                namedVars = unifyVars namedParams
                retVars = unifyVars ret
            in
            let vars1 = Map.unionWith Pos.choosePos paramsVars namedVars in
            Map.unionWith Pos.choosePos vars1 retVars
        TyRecord _ tm     -> unifyVars tm
        TyVar _ _         -> Map.empty
        TyUnifyVar pos i  -> Map.singleton i pos

instance UnifyVars Schema where
    unifyVars (Forall _ t) = unifyVars t

instance UnifyVars NamedType where
    unifyVars nt = case nt of
        ConcreteType ty -> unifyVars ty
        AbstractType _kind -> Map.empty


------------------------------------------------------------
-- Substitutions

-- | Subst is the type of a substitution map for unification vars.
--
--   For the substitution we accumulate in the `TI` context while
--   working, we maintain the following invariant:
--
--      If one unification var @b@ points to another unification
--      var @a@, @a < b@. That is, entries in the map that point
--      to other entries always point downwards. This prevents
--      generating cycles.
--
--   This does not apply to the smaller transient substitutions
--   we use in `generalize`, whose entries always map unification
--   vars to named vars.
--
type Subst = Map TypeIndex Type

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

instance (AppSubst t1, AppSubst t2) => AppSubst (Pos, (Pos, t1, t2)) where
    appSubst s (pos1, (pos2, a, b)) = (pos1, (pos2, appSubst s a, appSubst s b))

instance (AppSubst t) => AppSubst (Maybe (Pos, Text), t) where
    appSubst s (mbName, e) = (mbName, appSubst s e)

instance (AppSubst t) => AppSubst (PrimitiveLifecycle, t) where
    appSubst s (lc, x) = (lc, appSubst s x)

instance (AppSubst t) => AppSubst (Pos, PrimitiveLifecycle, Rebindable, t) where
    appSubst s (pos, lc, rb, x) = (pos, lc, rb, appSubst s x)

instance (Ord k, AppSubst a) => AppSubst (Map k a) where
    appSubst s = fmap (appSubst s)

instance AppSubst Expr where
    appSubst s expr = case expr of
        TSig pos e t           -> TSig pos (appSubst s e) (appSubst s t)
        Bool _ _               -> expr
        String _ _             -> expr
        Int _ _                -> expr
        Code _ _               -> expr
        CType _ _              -> expr
        Array pos es           -> Array pos (appSubst s es)
        Block pos (bs, e)      -> Block pos (appSubst s bs, appSubst s e)
        Tuple pos es           -> Tuple pos (appSubst s es)
        Record pos fs          -> Record pos (appSubst s fs)
        Index pos ar ix        -> Index pos (appSubst s ar) (appSubst s ix)
        Lookup pos rec fld     -> Lookup pos (appSubst s rec) fld
        TLookup pos tpl idx    -> TLookup pos (appSubst s tpl) idx
        Var _pos _x            -> expr
        Lambda pos mname pats ppats body ->
            let pats' = map (appSubst s) pats
                ppats' = Map.map (appSubst s) ppats
                body' = appSubst s body
            in
            Lambda pos mname pats' ppats' body'
        Application pos f v    ->
            Application pos (appSubst s f) (appSubst s v)
        Let pos dg e           ->
            Let pos (appSubst s dg) (appSubst s e)
        IfThenElse pos e e2 e3 ->
            IfThenElse pos (appSubst s e) (appSubst s e2) (appSubst s e3)

instance AppSubst Pattern where
    appSubst s pat = case pat of
        PWild pos mt  -> PWild pos (appSubst s mt)
        PVar allpos xpos x mt -> PVar allpos xpos x (appSubst s mt)
        PTuple pos ps -> PTuple pos (appSubst s ps)

instance AppSubst Stmt where
    appSubst s bst = case bst of
        StmtBind pos pat e       -> StmtBind pos (appSubst s pat) (appSubst s e)
        StmtLet pos rb dg        -> StmtLet pos rb (appSubst s dg)
        StmtCode allpos spos str -> StmtCode allpos spos str
        StmtImport pos imp       -> StmtImport pos imp
        StmtInclude pos file once -> StmtInclude pos file once
        StmtTypedef allpos apos a ty ->
            StmtTypedef allpos apos a (appSubst s ty)
        StmtPushdir pos dir      -> StmtPushdir pos dir
        StmtPopdir pos           -> StmtPopdir pos

instance AppSubst DeclGroup where
    appSubst s dg = case dg of
        Recursive ds -> Recursive (appSubst s ds)
        NonRecursive d -> NonRecursive (appSubst s d)

instance AppSubst Decl where
    appSubst s (Decl pos p mt e) =
        Decl pos (appSubst s p) (appSubst s mt) (appSubst s e)

instance AppSubst Type where
    appSubst s t = case t of
        TyCon pos tc ts -> TyCon pos tc (appSubst s ts)
        TyFunc pos ninfo params namedParams ret ->
            let params' = appSubst s params
                namedParams' = appSubst s namedParams
                ret' = appSubst s ret
            in
            TyFunc pos ninfo params' namedParams' ret'
        TyRecord pos fs -> TyRecord pos (appSubst s fs)
        TyVar _ _  -> t
        TyUnifyVar _ i -> case Map.lookup i s of
            Nothing -> t
            Just t' -> appSubst s t'

instance AppSubst Schema where
    appSubst s (Forall ns t) =
        Forall ns (appSubst s t)

instance AppSubst NamedType where
    appSubst s nt = case nt of
        ConcreteType ty -> ConcreteType $ appSubst s ty
        AbstractType kind -> AbstractType kind


------------------------------------------------------------
-- Pass context / monad

-- | The monad for this pass is "TI", which is composed of a read-only
--   part plus a read-write part that accumulates as we move through the
--   code.
--
--   Note that, for the time being at least, this monad cannot be in
--   IO, because we need to be able to use the typechecker in a pure
--   context when constructing the builtins table during startup. If
--   that becomes a prohibitive problem, we can rearrange the builtins
--   table construction, but that will be expensive.
--
newtype TI a = TI { unTI :: ReaderT RO (StateT RW Identity) a }
    deriving (Functor, Applicative, Monad, MonadReader RO, MonadState RW)

-- | The read-only portion
data RO = RO {
    -- | The variable availability (lifecycle set)
    tiPrimsAvail :: Set PrimitiveLifecycle,

    -- | The prettyprinter options
    tiPPOpts :: PPS.Opts
}

-- | The read-write portion
data RW = RW {
    -- | The variable typing environment (variable name to type scheme)
    tiVarEnv :: VarEnv,

    -- | The type environment: named type variables, which are either
    --   typedefs (map to ConcreteType) or abstract types (AbstractType)
    tiTyEnv :: TyEnv,

    -- | The next fresh unification var number
    tiNextTypeIndex :: TypeIndex,

    -- | The unification var substitution we're accumulating
    tiSubst :: Subst,

    -- | Any type errors and warnings we've generated so far
    --   These accumulate in reverse order; later messages are consed
    --   on the head of the list.
    tiErrors :: [(Pos, PPS.Doc)],
    tiWarnings :: [(Pos, PPS.Doc)]
}

-- | The result of a `TI` typechecker computation is either a list of
--   errors or a result value, along with (always) a list of warnings.
--   FUTURE: it would be better to preserve the ordering of warnings
--   and errors in a single list...
--
type MsgList = [(Pos, PPS.Doc)]
type Result a = (Either MsgList a, MsgList)

-- | Run the TI monad.
--
--   Note that we don't return the updated environments! This is a
--   manifestation of the unhealthy codependent relationship with the
--   interpreter.
--
runTI :: PPS.Opts -> Set PrimitiveLifecycle -> VarEnv -> TyEnv -> TI a ->
         Result a
runTI ppopts avail varenv tyenv m =
    let rw = RW {
            tiVarEnv = varenv,
            tiTyEnv = tyenv,
            tiNextTypeIndex = 0,
            tiSubst = Map.empty,
            tiErrors = [],
            tiWarnings = []
        }
        ro = RO {
            tiPrimsAvail = avail,
            tiPPOpts = ppopts
        }
        (result, rw') = runState (runReaderT (unTI m) ro) rw
        errs = reverse $ tiErrors rw'
        warns = reverse $ tiWarnings rw'
    in
    -- We succeed if and only if the error list is empty.
    case errs of
        [] -> (Right result, warns)
        _ -> (Left errs, warns)

-- | Run a speculative sub-action in the `TI` monad. Throw away
--   whatever it does, and return `True` if it succeeds (does
--   not generate new errors).
speculateTI :: TI a -> TI Bool
speculateTI m = do
    rw <- get
    ro <- ask
    let (_result, rw') = runState (runReaderT (unTI m) ro) rw
    pure $ length (tiErrors rw') == length (tiErrors rw)


------------------------------------------------------------
-- TI monad ops

-- | Enter a scope
pushScope :: TI ()
pushScope = do
    varenv <- gets tiVarEnv
    tyenv <- gets tiTyEnv
    let varenv' = ScopedMap.push varenv
        tyenv' = ScopedMap.push tyenv
    modify (\rw -> rw { tiVarEnv = varenv', tiTyEnv = tyenv' })

-- | Leave a scope
popScope :: TI ()
popScope = do
    varenv <- gets tiVarEnv
    tyenv <- gets tiTyEnv
    let varenv' = ScopedMap.pop varenv
        tyenv' = ScopedMap.pop tyenv
    modify (\rw -> rw { tiVarEnv = varenv', tiTyEnv = tyenv' })

-- | Get a fresh unification var number.
getFreshTypeIndex :: TI TypeIndex
getFreshTypeIndex = do
    next <- gets tiNextTypeIndex
    modify $ (\rw -> rw { tiNextTypeIndex = next + 1 })
    return next

-- | Construct a fresh type variable.
--
--   Collect the position that prompted us to make it; for example, if
--   we're the element type of an empty list we get the position of the
--   []. We haven't inferred anything, so use the InfFresh position.
--   This will cause the position of anything more substantive that gets
--   unified with it to be preferred. If no such thing happens though
--   this will be the position that gets attached to the quantifier
--   binding in generalize.
getFreshTyVar :: Pos -> TI Type
getFreshTyVar pos = TyUnifyVar (PosInferred InfFresh pos) <$> getFreshTypeIndex

-- | Construct a new type variable to use as a placeholder after an
--   error occurs. For now this is the same as other fresh type
--   variables, but I've split it out in case we want to distinguish
--   it in the future.
getErrorTyVar :: Pos -> TI Type
getErrorTyVar pos = getFreshTyVar pos

-- | Add an error message.
recordError :: Pos -> PPS.Doc -> TI ()
recordError pos err = do
    modify $ \rw -> rw { tiErrors = (pos, err) : tiErrors rw }

-- | Add an error message. Variant meant for use with prettyTypeDetails.
recordError' :: (Pos, PPS.Doc) -> TI ()
recordError' (pos, err) = recordError pos err

-- | Add a warning message.
recordWarning :: Pos -> PPS.Doc -> TI ()
recordWarning pos msg = do
    modify $ \rw -> rw { tiWarnings = (pos, msg) : tiWarnings rw }


------------------------------------------------------------
-- Resolution 

-- | Apply the current substitution with appSubst.
applyCurrentSubst :: AppSubst t => t -> TI t
applyCurrentSubst t = do
    s <- gets tiSubst
    return $ appSubst s t

-- | Apply the current typedef collection with `Util.substituteTyVars`.
--
--   The type t has already been checked, so it's ok to panic if it
--   refers to something in the typedef collection that's not visible.
resolveCurrentTypedefs :: Type -> TI Type
resolveCurrentTypedefs t = do
    avail <- asks tiPrimsAvail
    s <- gets tiTyEnv
    return $ Util.substituteTyVars avail s t

-- | Condense functions that return functions to a single function
--   type with more parameters. The passed-in position is used for
--   error reporting and should be the position of the expression
--   or other object whose type we're working on. (The position of
--   the type itself is not suitable; positions of types are meant
--   as further annotations to errors.)
condenseFunctions :: Pos -> Type -> TI Type
condenseFunctions errPos ty = case ty of
    TyFunc pos1 names1 params1 namedParams1 ret1 ->
        case ret1 of
            TyFunc _pos2 names2 params2 namedParams2 ret2 ->
                let dups = Map.intersection namedParams1 namedParams2 in
                case null dups of
                    True -> do
                        -- FUTURE: we could/should splice pos1 and
                        -- pos2... but we don't have a way to
                        -- represent disjoint position spans, so it's
                        -- only a good idea if they're "near" each
                        -- other. But they won't necessarily be, and
                        -- we have no way to figure that for the time
                        -- being.
                        let pos = pos1
                            names = names1 <> names2
                            params = params1 ++ params2
                            namedParams = Map.union namedParams1 namedParams2
                            ret = ret2
                            ty' = TyFunc pos names params namedParams ret
                        -- Try again in case there's more functions hiding
                        condenseFunctions errPos ty'
                    False -> do
                        let dups' = PP.hsep $ map PP.pretty $ Map.keys dups
                        recordError errPos $ "Function has duplicate" <+>
                                             "parameter names:" <+> dups'
                        getErrorTyVar pos1
            _ ->
                pure ty
    _ ->
        pure ty

-- | Apply both the current substitution and the current typedef
--   collection. Then if we get a function type, condense functions
--   that return functions to a single function type with more
--   parameters.
--
--   The position should be the position of the AST construct whose
--   type we're handling, and is used for error reporting.
expandFully :: Pos -> Type -> TI Type
expandFully pos t = do
    t' <- resolveCurrentTypedefs t
    t'' <- applyCurrentSubst t'
    condenseFunctions pos t''


------------------------------------------------------------
-- Further extraction / support logic

-- | Get the unification vars that are used in the current variable typing
--   and named type environments.
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
-- dholland 20251120: If it does turn out to be a problem, we can now
-- also get shadowed values out of the environment by adding a suitable
-- variant of @elems@ to `ScopedMap`.
--
-- Note that we apply the current substitution first. This means that
-- the caller must also apply the current substitution before reasoning
-- about what unification vars do and don't appear.
--
-- Returns a map of the index number to the occurrence position.
unifyVarsInEnvs :: TI (Map TypeIndex Pos)
unifyVarsInEnvs = do
    venv <- gets tiVarEnv
    tenv <- gets tiTyEnv
    vtys <- mapM applyCurrentSubst $ ScopedMap.allElems venv
    ttys <- mapM applyCurrentSubst $ ScopedMap.allElems tenv
    return $ Map.unionWith Pos.choosePos (unifyVars vtys) (unifyVars ttys)

-- | Get the named type vars that occur as keys in the current type name
--   environment.
namedVarDefinitions :: TI (Set Name)
namedVarDefinitions = do
    env <- gets tiTyEnv
    return $ ScopedMap.allKeysSet env

-- | Get all the bindings in a pattern.
patternBindings :: Pattern -> [(Name, Pos, Maybe Type)]
patternBindings pat = case pat of
    PWild _ _mt -> []
    PVar _ xpos x mt -> [(x, xpos, mt)]
    PTuple _ ps -> concatMap patternBindings ps

-- | Get all the bindings in a pattern, using a separate passed-in
--   schema to get the types. Ignore the types in the pattern.
--
-- XXX: is that reasonable? Should probably assert that the schema
-- matches the types in the pattern, unless the pattern hasn't already
-- been checked yet, and that seems like it would be a bug.
--
-- Note that if the pattern is a tuple and the schema is not a tuple
-- type, we return nothing. Presumably in this case a type error has
-- already been generated and we don't need another one? But it would
-- probably be a good idea to check up on that. XXX
--
-- Alternatively if the pattern has had its types filled in, this
-- should not be different from the plain patternBindings and should
-- probably just be removed.
--
patternBindingsWithSchema :: Pattern -> Schema -> [(Name, Pos, Schema)]
patternBindingsWithSchema pat sch = case pat of
    PWild _ _ -> []
    PVar _ xpos x _ -> [(x, xpos, sch)]
    PTuple _ ps ->
      case sch of
        Forall vs t -> case t of
            TyCon _pos (TupleCon _) ts' ->
                let once pat' t' =
                      patternBindingsWithSchema pat' (Forall vs t')
                in
                concat $ zipWith once ps ts'
            _ -> []


------------------------------------------------------------
-- Unification

--
-- Error reporting.
--
-- When we find a mismatch, we have potentially recursed arbitrarily
-- deeply into the original type. We need to print the specific types
-- we trip on (this is important if they are e.g. elements in a large
-- system of nested records and typles) but we also want to print the
-- rest of the original context as well.
--
-- Therefore, as we recurse into the type we accumulate a list of the
-- expected/found pairs that we have seen; and when we get an error,
-- we print all of them along with the rest of the error message.
--
-- Empty strings are inserted between pairs to make the output more
-- readable.
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
-- I keep going back and forth on whether the larger types should be
-- printed first (as is) or last (needs a reverse in
-- `prettyEnclosing`).
--

-- | Print a list of enclosing types.
prettyEnclosing :: PPS.Opts -> [(Type, Type)] -> PPS.Doc
prettyEnclosing ppopts tys =
    let once (tyexp, tyfound) =
          let tyexp' = prettyType ppopts tyexp
              tyfound' = prettyType ppopts tyfound
              expectedShort  = "Expected:" <+> tyexp'
              foundShort     = "Found:   " <+> tyfound'
              -- Use of nest here allows the open-brace of records to
              -- go on the same line, which ends up looking better
              expectedLong   = "Expected:" <+> PP.nest 3 tyexp'
              foundLong      = "Found:" <+> PP.nest 3 tyfound'
              expected = PP.group $ PP.flatAlt expectedLong expectedShort
              found = PP.group $ PP.flatAlt foundLong foundShort
          in
          expected <> PP.hardline <> found <> PP.hardline <> ""
    in
    PP.vsep $ map once tys

-- | Print details of a type. This prints the provenance info
--   we carry in type positions.
prettyTypeDetails :: PPS.Opts -> Type -> (Pos, PPS.Doc)
prettyTypeDetails ppopts ty =
    let (pos, what) = case Pos.getPos ty of
           PosInferred InfFresh p ->
               (p, "a fresh type variable introduced here")
           PosInferred InfTerm p ->
               (p, "the type of this term")
           PosInferred InfContext p ->
               (p, "the context of the term")
           p ->
               (p, "this type annotation")
    in
    let ty' = prettyType ppopts ty
        what' = "arises from" <+> what

        -- Deliberately render and re-docify the type, and generate a
        -- multi-line message only if the type comes out as multiple
        -- lines when rendered on its own. This is kind of gross, but
        -- the prettyprinter library does not give much in the way of
        -- formatting control, and if we just do things its way we
        -- pretty much always get a multiline message, even for very
        -- short types like (), because what' coupled
        -- with the position text at the beginning of the line is long
        -- enough to make the prettyprinter library think the message
        -- ought to be multiline. Perhaps the right way to deal with
        -- this problem is to force it to use a different notion of
        -- what constitutes a "long" line when dealing with error
        -- messages rather than program text; but for the time being
        -- at least we have no useful infrastructure to support that.
        -- So instead generate our own faux "reactive" layout. XXX.
        --
        -- If you find a way to fix this better, please also fix the
        -- analogous code for "Too many arguments to function" below.
        --
        msg = case map PP.pretty $ Text.lines $ PPS.renderText ppopts ty' of
            [ty''] -> "The type" <+> ty'' <+> what'
            ty'' -> "The type" <+> PP.nest 3 (PP.vsep ty'' <> PP.line <> what')
    in
    (pos, msg)

-- | Insert an entry in the substitution we're carrying around. Raw
--   version; everyone except `resolveVar` should call `resolveVar`
--   instead.
addResolution :: TypeIndex -> Type -> TI ()
addResolution i ty = do
    subst <- gets tiSubst
    let subst' = Map.insert i ty subst
    modify (\rw -> rw { tiSubst = subst' })

-- | Resolve a unification var: update the table we're carrying around
--   to hold the new definition for @i@.
resolveVar :: Pos -> TypeIndex -> Type -> TI ()
resolveVar pos'i i ty = do
    -- Check if we should prefer using t1 to t2 as an expansion.
    -- Return the unification variable ID inside t2.
    let prefer t1 t2 = case (t1, t2) of
          (TyUnifyVar _ j, TyUnifyVar pos'k k)
              | j < k -> Just (pos'k, k) -- prefer t1/j
              | otherwise -> Nothing
          (TyUnifyVar{}, _) -> Nothing
          (_, TyUnifyVar pos'j j) -> Just (pos'j, j) -- prefer t1
          (_, _) ->
              -- We should only ever get here for convertible types;
              -- we could check that; but we don't have an easy way
              -- to at the moment, so don't bother.
              Nothing

    -- Insert the new result. Shuffle around what's already there
    -- as needed to preserve the ordering invariant.
    case ty of
        TyUnifyVar pos'j j | j > i ->
            -- Maintain the ordering invariant for unification vars
            -- pointing at each other.
            resolveVar pos'j j (TyUnifyVar pos'i i)
        _ -> do
            -- Check what's in slot i.
            subst <- gets tiSubst
            case Map.lookup i subst of
                Nothing ->
                    -- Nothing already there, resolve to what we've got
                    addResolution i ty
                Just ty'already ->
                    -- There's already a type there. Check if it's a
                    -- unification var we should replace.
                    case prefer ty ty'already of
                        Nothing ->
                            -- There's a type already there, and we
                            -- shouldn't replace it with @ty@. If @ty@
                            -- is a unification var, resolve @ty@ to
                            -- the type already there. Otherwise, both
                            -- types are real types. We could assert
                            -- that they're convertible, but we don't
                            -- have an easy way to do that. There is
                            -- no need to do anything else.
                            case ty of
                                TyUnifyVar pos'j j ->
                                    resolveVar pos'j j ty'already
                                _ ->
                                    pure ()
                        Just (pos'j, j) -> do
                            -- There's a type already there, and we
                            -- should replace it because it's a
                            -- unification var. Do that, then resolve
                            -- its unification var too.
                            addResolution i ty
                            resolveVar pos'j j ty

--
-- | Unify two types.
--
-- When typechecking an expression the first type argument (@exp@)
-- should be the type expected from the context, and the second
-- (@found@) should be the type found in the expression appearing in
-- that context. The position argument should be the position at which
-- any error should be reported, typically the position of the program
-- element whose type is t2.
--
-- If it doesn't work, the message generated will be of the form "pos:
-- found t2, expected t1".
--
-- For example, when checking the second argument of a function
-- application (Application _pos e1 e2) checking e1 gives rise to an
-- expected type for e2. So when unifying that with the result of
-- checking e2,
--    - the t1 argument should be the expected type arising from e1,
--    - the t2 argument should be the type returned by checking e2,
--    - and the position argument should be the position of e2, not
--      the position of the enclosing apply node.
--
-- Other cases should pass the arguments analogously. Some may still be
-- backwards.
--
-- Error messages are indented (all but the first line) by four spaces
-- because the first line sometimes ends up indented by two when it
-- ultimately gets printed, and we want the grouping to be clearly
-- recognizable.
--
unify :: Type -> Pos -> Type -> TI ()
unify exp0 pos found0 = visit [] exp0 found0
  where
    visit :: [(Type, Type)] -> Type -> Type -> TI ()
    visit encs expectBase foundBase = do
        -- Use pos as the failure position for either type; they're the
        -- same type after all, and any position that gives rise to it
        -- should be good enough if expandFully croaks. (Hopefully.)
        expect <- expandFully pos expectBase
        found <- expandFully pos foundBase

        -- | Fail with expected/found types
        let reject msg more = do
              ppopts <- asks tiPPOpts
              encs' <- do
                  let once (t1, t2) = do
                        t1' <- expandFully pos t1
                        t2' <- expandFully pos t2
                        pure (t1', t2')
                  mapM once encs
              let body = PP.vsep $ more ++ [
                      prettyEnclosing ppopts ((expect, found) : encs')
                   ]
              recordError pos $ "Error:" <+> msg <> PP.line <> PP.indent 4 body

              let (pos'expect, expect') = prettyTypeDetails ppopts expect
                  (pos'found, found') = prettyTypeDetails ppopts found
              recordError pos'expect $ "Note:" <+> expect'
              -- Attach a blank line to this message so there's a separator
              -- between it and the next type error. XXX: we should have a
              -- less ad hoc way to do this.
              recordError pos'found $ "Note:" <+> found' <> PP.hardline <> ""

        -- | We would like to resolve unification var @i@ to type @ty@.
        --   Make sure this is well formed.
        --
        --   Does not handle the case where t _is_ TyUnifyVar i; there's
        --   a separate case for that.
        --
        let checkOccurs pos'i i ty =
              -- Collect the unification vars in ty, and check for an appearance
              -- of i.
              case Map.lookup i $ unifyVars ty of
                  Nothing -> pure ty
                  Just _otherpos -> do
                      ppopts <- asks tiPPOpts
                      let expect' = prettyType ppopts expect
                          found' = prettyType ppopts found
                          i' = prettyType ppopts $ TyUnifyVar pos'i i
                          ty' = prettyType ppopts ty

                      _ <- reject "Occurs check failure." [
                          "Cannot unify" <+> expect' <+>
                          "with" <+> found' <+> "because" <+> i' <+>
                          "appears within" <+> ty' <> "."
                       ]
                      getErrorTyVar pos'i

        -- recurse into one nested type
        let recOnce exp' found' =
              visit ((expect, found) : encs) exp' found'

        -- recurse into a list of types
        let recList exps' founds' =
              zipWithM_ (visit ((expect, found) : encs)) exps' founds'


        case (expect, found) of
            (TyUnifyVar _ i, TyUnifyVar _ j) | i == j ->
                -- same unification var, nothing to do
                pure ()

            (TyUnifyVar pos'i i, _) -> do
                -- one side is a unification var, resolve it
                found' <- checkOccurs (Pos.getPos found) i found
                resolveVar pos'i i found'

            (_, TyUnifyVar pos'i i) -> do
                -- the other side is a unification var, resolve it
                expect' <- checkOccurs (Pos.getPos expect) i expect
                resolveVar pos'i i expect'

            (TyFunc pos'expect _ expParams expNamedParams expRet,
             TyFunc pos'found _ foundParams foundNamedParams foundRet) -> do
                -- First, unify the named parameters.
                --
                -- (We handle the named parameters first because because
                -- they don't carry into the return value like curried
                -- positional parameters.)
                --
                -- XXX: should we insist that both sides have the same named
                -- parameters, or take the union of them? Allowing functions to
                -- grow extra named (thus optional) parameters they ignore is
                -- sound, but possibly unexpected/weird, so for now require them
                -- to match exactly.
                let expNames = Map.keysSet expNamedParams
                    foundNames = Map.keysSet foundNamedParams
                if expNames /= foundNames then do
                    ppopts <- asks tiPPOpts
                    let expect' = prettyType ppopts expect
                        found' = prettyType ppopts found
                        expMissing = Map.difference foundNamedParams expNamedParams
                        foundMissing = Map.difference expNamedParams foundNamedParams
                        prettyMissing (name, ty) =
                            let ty' = prettyType ppopts ty in
                            PP.pretty name <+> ":" <+> ty'
                        prettyMissingList fty' ms = case ms of
                            [] ->
                                []
                            _ ->
                                let ms' = PP.vsep $ map prettyMissing ms
                                    line1 = "Missing from" <+> fty' <> ":"
                                    lines2 = PP.indent 3 ms'
                                in
                                [line1 <> PP.line <> lines2]
                        expMissing' = prettyMissingList expect' $ Map.toList expMissing
                        foundMissing' = prettyMissingList found' $ Map.toList foundMissing
                        missing' = expMissing' ++ foundMissing'
                    reject "Mismatched named parameters." missing'

                else do
                    -- In principle when you have checked that the keys
                    -- match, you can do zip (Map.toList namedParams1)
                    -- (Map.toList namedParams2) and have things match up
                    -- correctly, but it makes me nervous, so do it like
                    -- this instead.
                    let allNamedParams =
                            Map.intersectionWith (,) expNamedParams foundNamedParams
                        (expNP, foundNP) = unzip $ Map.elems allNamedParams
                    recList expNP foundNP

                -- Now unify as many positional params as possible. This
                -- also produces the remainder types, basically the return
                -- type. If one function is a -> b, and the other function
                -- is a -> c -> d, the remainder types are b and c -> d
                -- respectively.

                let nExp = length expParams
                    nFound = length foundParams
                (expRemainder, foundRemainder) <- do
                    if nExp < nFound then do
                        let foundParamsL = take nExp foundParams
                            foundParamsR = drop nExp foundParams
                        recList expParams foundParamsL
                        -- we've used up expParams.
                        let ty' = TyFunc pos'found noNames foundParamsR Map.empty foundRet
                        pure (expRet, ty')
                    else if nFound > nExp then do
                        -- unfortunately we need two copies of this because
                        -- left vs. right side is semantically significant :-(
                        let expParamsL = take nFound expParams
                            expParamsR = drop nFound expParams
                        recList expParamsL foundParams
                        -- we've used up foundParams.
                        let ty' = TyFunc pos'expect noNames expParamsR Map.empty expRet
                        pure (ty', foundRet)
                    else do
                        recList expParams foundParams
                        -- we've used up both expParams and foundParams.
                        pure (expRet, foundRet)

                -- now unify the remainders / return types
                recOnce expRemainder foundRemainder

            (TyRecord _ expFields, TyRecord _ foundFields)
              | Map.keys expFields /= Map.keys foundFields ->
                -- records with different keys
                reject "Record field names do not match." []

              | otherwise ->
                -- records with the same field names, try unifying the field types
                recList (Map.elems expFields) (Map.elems foundFields)

            (TyCon _ expTC expTS, TyCon _ foundTC foundTS) | expTC == foundTC -> do
                -- same type constructor, unify the args
                when (length expTS /= length foundTS) $ do
                    -- This case is unreachable.
                    --
                    -- Every distinct type constructor has a definite
                    -- arity (tuples of different lengths are not the same
                    -- type constructor) and every type is supposed to
                    -- pass `checkType` before we do anything more
                    -- significant with it; that does a kind check, and on
                    -- failure produces a fresh unification var that can't
                    -- cause further trouble.
                    --
                    -- Therefore, if we get here, something's broked and we should
                    -- panic.
                    --
                    ppopts <- asks tiPPOpts
                    let expTS'   = "LHS:" : map (\t -> "   " <> ppType ppopts t) expTS
                        foundTS' = "RHS:" : map (\t -> "   " <> ppType ppopts t) foundTS
                    let nexpect'   = Text.pack $ show $ length expTS
                        nfound' = Text.pack $ show $ length foundTS
                        heading = "Mismatched type constructor arguments: " <>
                                  "expected " <> nexpect' <> ", found " <> nfound'
                    panic "unify" (heading : expTS' ++ foundTS')

                recList expTS foundTS

            (TyVar _ a, TyVar _ b) | a == b ->
                -- Same named variable, nothing to do
                pure ()

            (_, TyFunc{}) ->
                -- If we expected a scalar and found a function, speculate that
                -- someone forgot a function argument earlier.
                reject "Type mismatch."
                    ["Perhaps a function was not given enough arguments?"]

            (_, _) ->
                -- Did not work
                reject "Type mismatch." []


-- Check if two types match but don't actually unify them
-- (that is, throw away any changes or diagnostics that appear)
--
-- This is inelegant, and used for some workaround logic to decide
-- which unifications to attempt to avoid failures on things we don't
-- want to make fatal just yet. It should be removed when no longer
-- needed.
matches :: Pos -> Type -> Type -> TI Bool
matches pos t1 t2 =
    speculateTI $ unify t1 pos t2


------------------------------------------------------------
-- Inspect for free type variables

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
--    zero or more times, Lambda _pos <params> <named-params> <expr'>
--    then optionally, TSig _pos <expr''> <return-type>
--
-- so we need any free type variables in
--    - <function-name-pattern>
--    - <return-type>
--    - all <params> and <named-params>
--
-- On the plus side this will also then work when people write
-- otherwise annoying things like
--    let f (x: a) = \(y: b) -> (a, b)
--
-- We extract the type variables with the position of their
-- initial mention, and the kind that appears to apply.
--
-- If the kind usage is inconsistent, the declaration involved will
-- fail kind-checking downstream. So it doesn't matter which of the
-- multiple usages we return, and we'll leave that unspecified.

-- Get the free type variables found in a Type.
inspectTypeFTVs :: Kind -> Type -> TI (Map Name (Pos, Kind))
inspectTypeFTVs kind ty = case ty of
    TyCon _pos ctor args -> do
        let kinds = lookupTyCon ctor
        Map.unions <$> zipWithM inspectTypeFTVs kinds args
    TyFunc _pos _ params namedParams ret ->
        let np = Map.elems namedParams in
        Map.unions <$> mapM (inspectTypeFTVs kindStar) (ret : params ++ np)
    TyRecord _pos fields ->
        Map.unions <$> traverse (inspectTypeFTVs kindStar) fields
    TyUnifyVar _pos _x ->
        return Map.empty
    TyVar pos x -> do
        tyenv <- gets tiTyEnv
        case ScopedMap.lookup x tyenv of
            Nothing -> return $ Map.singleton x (pos, kind)
            Just _ -> return $ Map.empty

-- Get the free type variables found in a Maybe Type.
inspectMaybeTypeFTVs :: Kind -> Maybe Type -> TI (Map Name (Pos, Kind))
inspectMaybeTypeFTVs kind mty = case mty of
    Nothing -> return Map.empty
    Just ty -> inspectTypeFTVs kind ty

-- Get the free type variables found in a Pattern.
inspectPatternFTVs :: Pattern -> TI (Map Name (Pos, Kind))
inspectPatternFTVs pat = case pat of
    PWild _pos mty -> inspectMaybeTypeFTVs kindStar mty
    PVar _allpos _xpos _x mty -> inspectMaybeTypeFTVs kindStar mty
    PTuple _pos subpats ->
        Map.unions <$> mapM inspectPatternFTVs subpats

-- Get the free type variables found in a parameter list, aka [Pattern].
inspectParamsFTVs :: [Pattern] -> TI (Map Name (Pos, Kind))
inspectParamsFTVs pats =
    Map.unions <$> mapM inspectPatternFTVs pats

-- Get the free type variables found in a named parameter list.
inspectNamedParamsFTVs ::
      Map Text (Pos, (Pos, Expr, Pattern)) ->
      TI (Map Name (Pos, Kind))
inspectNamedParamsFTVs params =
    --
    -- Note: it's possible we should also allow type variables to
    -- appear in the default value expressions for optional arguments.
    -- For the time being we don't.
    --
    -- That means that you can't write
    --   let foo x?=(undefined : a) = ...
    -- ...you should instead write that as
    --   let foo (x?=undefined : a) = ...
    -- that is, put the type on the parameter and not the value.
    --
    let extract (_x, (_xpos, (_allpos, _e, pat))) = pat
        pats = map extract $ Map.toList params
    in
    inspectParamsFTVs pats

-- Get the free type variables found in a chain of Lambda Exprs.
-- Also return the body expression found on the inside of the chain
-- for possible further analysis.
inspectLambdaFTVs :: Expr -> TI (Expr, Map Name (Pos, Kind))
inspectLambdaFTVs e0 = case e0 of
    Lambda _fpos _mname params namedParams e1 -> do
        paramFTVs <- inspectParamsFTVs params
        namedFTVs <- inspectNamedParamsFTVs namedParams
        (e1', bodyFTVs) <- inspectLambdaFTVs e1
        return (e1', Map.union (Map.union paramFTVs namedFTVs) bodyFTVs)
    _ ->
        return (e0, Map.empty)

-- Get the free type variables found in a Decl.
inspectDeclFTVs :: Decl -> TI (Map Name (Pos, Kind))
inspectDeclFTVs (Decl _dpos pat _mty e0) = do
    nameFTVs <- inspectPatternFTVs pat
    (e1, argFTVs) <- inspectLambdaFTVs e0
    retFTVs <- case e1 of
        TSig _tspos _e2 ty -> inspectTypeFTVs kindStar ty
        _ -> return Map.empty
    return $ Map.unions [nameFTVs, argFTVs, retFTVs]



------------------------------------------------------------
-- Main recursive pass

type OutExpr = Expr
type OutStmt = Stmt

--
-- Expressions
--

-- | Take a struct field binding (name and expression) and return the
-- updated binding as well as the member entry for the enclosing
-- struct type.
inferField :: (Name, Expr) -> TI ((Name, OutExpr), (Name, Type))
inferField (n,e) = do
    (e', t) <- inferExpr e
    return ((n, e'), (n, t))

-- | Add x with type ty to the environment.
addVar :: Name -> Pos -> Rebindable -> Schema -> TI ()
addVar x pos rb ty = do
    env <- gets tiVarEnv
    let env' = ScopedMap.insert x (pos, Current, rb, ty) env
    modify (\rw -> rw { tiVarEnv = env' })

-- | Add xs with type tys to the environment.
addVars :: Rebindable -> [(Name, Pos, Schema)] -> TI ()
addVars rb bindings = mapM_ (\(x, pos, ty) -> addVar x pos rb ty) bindings

-- | Add all the vars in a pattern to the environment.
--
-- (Note that the pattern should have already been processed so it
-- contains types; hence the irrefutable Just t.)
addPattern :: Pattern -> TI ()
addPattern pat = do
    let bindings =
          [ (x, pos, tMono t) | (x, pos, Just t) <- patternBindings pat ]
    addVars ReadOnlyVar bindings

-- | Add all the vars in a list of patterns to the environment, while
--   running m.
--
--   (Note that the patterns should have already been processed so they
--   contain types; hence the irrefutable Just t.)
addPatterns :: [Pattern] -> TI ()
addPatterns pats = do
    let bindings pat =
          [ (x, pos, tMono t) | (x, pos, Just t) <- patternBindings pat ]
        allbindings = concatMap bindings pats
    addVars ReadOnlyVar allbindings

-- | Add all the vars in a pattern to the environment.
--
-- Variant version that uses the passed-in schema to produce the types
-- and ignoring the types already loaded into the pattern.
addPatternSchema :: Pattern -> Rebindable -> Schema -> TI ()
addPatternSchema pat rb ty = addVars rb bindings
    where bindings = patternBindingsWithSchema pat ty

-- | Add all the vars in a declaration to the environment.
--
-- Do nothing if there's no type schema in this declaration yet.
-- XXX: is that reasonable? shouldn't it panic?
addDecl :: Rebindable -> Decl -> TI ()
addDecl rb d = case d of
    Decl _ _ Nothing _ -> return ()
    Decl _ p (Just s) _ -> addPatternSchema p rb s

-- | Add all the vars in a declaration group to the environment.
addDeclGroup :: Rebindable -> DeclGroup -> TI ()
addDeclGroup rb dg = case dg of
    NonRecursive d -> addDecl rb d
    Recursive ds -> mapM_ (addDecl rb) ds

-- | Add some abstract type variables.
addAbstractTyVars :: Map Name (Pos, Kind) -> TI ()
addAbstractTyVars vars = do
    let insertOne x (_pos, kind) tyenv =
            ScopedMap.insert x (Current, AbstractType kind) tyenv
        insertAll tyenv =
            Map.foldrWithKey insertOne tyenv vars
    tyenv <- gets tiTyEnv
    let tyenv' = insertAll tyenv
    modify (\rw -> rw { tiTyEnv = tyenv' })

-- | Infer the type for an expression.
--
inferExpr :: Expr -> TI (OutExpr, Type)
inferExpr expr = case expr of
    Bool pos b    -> return (Bool pos b, tBool (PosInferred InfTerm pos))
    String pos s  -> return (String pos s, tString (PosInferred InfTerm pos))
    Int pos i     -> return (Int pos i, tInt (PosInferred InfTerm pos))
    Code pos s    -> return (Code pos s, tTerm (PosInferred InfTerm pos))
    CType pos s   -> return (CType pos s, tType (PosInferred InfTerm pos))

    Array pos [] -> do
        a <- getFreshTyVar pos
        return (Array pos [], tArray (PosInferred InfTerm pos) a)

    Array pos (e:es) -> do
        (e',t) <- inferExpr e
        es' <- mapM (\e1 -> checkExpr e1 t) es
        return (Array pos (e':es'), tArray (PosInferred InfTerm pos) t)

    Block pos body -> do
        ctx <- getFreshTyVar pos
        tyResult <- getFreshTyVar pos
        let ty = tBlock (PosInferred InfTerm pos) ctx tyResult
        pushScope
        body' <- inferBlock pos ctx ty body
        popScope
        return (Block pos body', ty)

    Tuple pos es -> do
        (es',ts) <- unzip <$> mapM inferExpr es
        return (Tuple pos es', tTuple (PosInferred InfTerm pos) ts)

    Record pos fs -> do
        (nes',nts) <- unzip `fmap` mapM inferField (Map.toList fs)
        let ty = TyRecord (PosInferred InfTerm pos) $ Map.fromList nts
        return (Record pos (Map.fromList nes'), ty)

    -- XXX this is currently unreachable because there's no concrete
    -- syntax for it; the parser will never produce it.
    Index pos ar ix -> do
        (ar',at) <- inferExpr ar
        ix'      <- checkExpr ix (tInt (PosInferred InfContext (Pos.getPos ix)))
        t        <- getFreshTyVar (Pos.getPos ix')
        let pos'ar = Pos.getPos ar'
            pos'ty = PosInferred InfContext pos'ar
        unify (tArray pos'ty t) pos'ar at
        return (Index pos ar' ix', t)

    Lookup pos e n -> do
        (e1,t) <- inferExpr e
        t1 <- expandFully (Pos.getPos e1) t
        elTy <- case t1 of
            TyRecord typos fs
              | Just ty <- Map.lookup n fs -> do
                  return ty
              | otherwise -> do
                  let n' = PP.pretty n
                  recordError pos $
                      "Record type has no field named" <+> n'
                  getErrorTyVar typos
            TyUnifyVar _ _ -> do
                let n' = PP.pretty n
                recordError pos $
                    "Cannot infer a record type for field" <+> n' <>
                    "; please use a type annotation"
                getErrorTyVar pos
            _ -> do
                ppopts <- asks tiPPOpts
                let t1' = prettyType ppopts t1
                recordError pos $
                    "Record lookup on non-record value of type" <+> t1'
                getErrorTyVar pos
        return (Lookup pos e1 n, elTy)

    TLookup pos e i -> do
        (e1,t) <- inferExpr e
        t1 <- expandFully (Pos.getPos e1) t
        elTy <- case t1 of
            TyCon typos (TupleCon n) tys
              | i < n ->
                  return (tys !! fromIntegral i)
              | otherwise -> do
                  let i' = PP.viaShow i
                      n' = PP.viaShow n
                  recordError pos $
                      "Tuple index" <+> i' <+> "out of bounds; limit is" <+> n'
                  getErrorTyVar typos
            TyUnifyVar _ _ -> do
                let i' = PP.viaShow i
                recordError pos $
                    "Cannot infer tuple arity for lookup of element" <+> i' <>
                    "; please use a type annotation"
                getErrorTyVar pos
            _ -> do
                ppopts <- asks tiPPOpts
                let t1' = prettyType ppopts t1
                recordError pos $ "Tuple lookup on non-tuple value of type" <+>
                                  t1'
                getErrorTyVar pos
        return (TLookup pos e1 i, elTy)

    Var pos x -> do
        let x' = PP.dquotes (PP.pretty x)
        avail <- asks tiPrimsAvail
        env <- gets tiVarEnv
        case ScopedMap.lookup x env of
            Nothing -> do
                recordError pos $ "Unbound variable:" <+> x'
                t <- getFreshTyVar pos
                return (Var pos x, t)
            Just (_prevpos, lc, _rebindable, Forall as t)
              | Set.member lc avail -> do
                  when (Util.isDeprecated lc) $
                      case t of
                      TyFunc _typos _ _params _namedparams _ret ->
                          recordWarning pos $ "Function is deprecated:" <+> x'
                      _ ->
                          recordWarning pos $ "Value is deprecated:" <+> x'

                  -- get a fresh tyvar for each quantifier binding, convert
                  -- to a name -> ty map, and substitute the fresh tyvars
                  let once (apos, a) = do
                        at <- getFreshTyVar apos
                        return (a, (Current, ConcreteType at))
                  substs <- mapM once as
                  let t' = Util.substituteTyVars' avail (Map.fromList substs) t
                  return (Var pos x, t')
              | otherwise -> do
                  recordError pos $ "Inaccessible variable:" <+> x'
                  let how = if lc == HideDeprecated then "deprecated"
                            else "experimental"
                      cmd = "`enable_" <> how <> "`."
                  recordError pos $ "This command is available only" <+>
                                    "after running" <+> cmd

                  t' <- getFreshTyVar pos
                  return (Var pos x, t')

    Lambda pos mname params namedParams body -> do
        pushScope
        let onePositional param = do
              (paramty, param') <- inferPattern ReadOnlyVar param
              addPattern param'
              pure (paramty, param')
        (paramtys, params') <- unzip <$> mapM onePositional params
        let oneNamed :: (Name, (Pos, (Pos, Expr, Pattern))) ->
              TI ((Name, Type), (Name, (Pos, (Pos, Expr, Pattern))))
            oneNamed (name, (namepos, (allpos, e, param))) = do
              (paramty, param') <- inferPattern ReadOnlyVar param
              e' <- checkExpr e paramty
              addPattern param'
              pure ((name, paramty), (name, (namepos, (allpos, e', param'))))
        (namedParamtys, namedParams') <-
            unzip <$> mapM oneNamed (Map.toList namedParams)

        (body', tybody) <- inferExpr body
        popScope

        when (null params' && not (null namedParams')) $ do
            recordError pos $ "Functions may not have only named" <+>
                              "parameters; add ()"

        -- XXX neither InfContext nor InfTerm is quite right here, but
        -- InfContext is what we were using before. Properly the
        -- position of the type of the lambda should include the
        -- parameters, maybe an InfLambda constructor that records
        -- positions for the parameters and return type that you can pop
        -- as the parameters get applied.  The current behavior is
        -- optimized for the common case where you write "let f x y =
        -- plop x y 1 2 3" and leave off the last argument of plop by
        -- accident, so the return type of f unexpectedly becomes a
        -- function, and we'll cite the type of "plop x y 1 2 3" which
        -- is missing an arg.
        --
        -- Note: we generate [] for the namelist field of the function
        -- type because we're downstream of the only thing that uses it.
        let e' = Lambda pos mname params' (Map.fromList namedParams') body'
            pos'ty = PosInferred InfContext (Pos.getPos body')
            namedParamtys' = Map.fromList namedParamtys
            ty = tFun pos'ty noNames paramtys namedParamtys' tybody
        return (e', ty)

    Application pos f args0 -> do
        -- The way this works is:
        --    - First we infer a type for the thing we're calling (the
        --      expression f). In the common case, it's just a function
        --      name and we'll get a function type back from the
        --      environment.
        --    - Then we resolve that type fully by substituting etc so
        --      we can look at it.
        --    - Then we infer types for all the arguments.
        --    - Then we use checkCall to check the actual call, passing
        --      the function type and the arguments/argument types.  (We
        --      want the argument expressions too, because we want their
        --      positions for some of the failure cases.)
        --    - checkCall examines the type of the callee, and if it's a
        --      function type unifies the parameter types with the
        --      argument type we got, and then:
        --         - if there are more parameters left, returns a
        --           partially applied function type;
        --         - if there are more arguments left, recurses to try
        --           calling the result type with the rest of the
        --           arguments;
        --         - if we exactly consumed all the arguments, just
        --           returns the result type.
        --    - If it _wasn't_ a function type but an unresolved
        --      unification var, cons up a function type from the
        --      arguments and unify that with the unification var.
        --    - If it was anything else, we tried to call a
        --      non-function, so complain. Handle the error paths for
        --      this being the first go vs. not differently, because one
        --      is calling a non-function and the other is giving too
        --      many arguments.
        --
        -- There's an oddity that comes up when you have a function that
        -- polymorphically returns its last parameter and you pass it
        -- too many arguments. This causes us to infer a type t1 -> t2
        -- for that last parameter (so that it can accept the excess
        -- argument) and then when it isn't actually a function the
        -- resulting error message readily becomes confusing. This can
        -- be staved off by doing the unifications just so (in
        -- particular, if we have f x y = y, unify the type of (f x)
        -- with a -> b, and then unify b with the type of y _before_
        -- unifying it with a type a' -> b' to accept the next argument,
        -- we hit the expected path for too many arguments) but in the
        -- current formulation with multiple-argument functions we can't
        -- readily do it that way. What happens below is that we make a
        -- second go through checkCall and it goes to the TyUnifyVar
        -- case, and by being careful about the positions it reports we
        -- manage to produce an ok message. There is a test in
        -- test_type_errors to make sure the message for this particular
        -- case doesn't regress.

        let checkCall isFirst origTy ty arginfo namedArginfo = case ty of
              TyFunc typos _ params namedParams ret -> do
                  -- We have a function type, check it in detail.
                  let nparams = length params
                      nargs = length arginfo
                  -- Unify all the positional args we have against their params.
                  let oneArg typaram (arg, tyarg) =
                          unify typaram (Pos.getPos arg) tyarg
                  zipWithM_ oneArg params arginfo

                  -- Unify all the named args we have against their params.
                  let oneNamedArg typaram (_namepos, arg, tyarg) =
                          unify typaram (Pos.getPos arg) tyarg
                  zipByKeyWithM_ oneNamedArg namedParams namedArginfo

                  -- Compute the named parameters and named arguments we
                  -- haven't used.
                  let namedParams' = dropKeys (Map.keys namedArginfo) namedParams
                      namedArginfo' = dropKeys (Map.keys namedParams) namedArginfo

                  let objectToLeftoverArgs = do
                        let once (name, (namepos, _arg, _ty)) =
                              recordError namepos $ "Invalid named argument" <+>
                                                    PP.pretty name <> ":" <+>
                                                    "No such named parameter"
                        mapM_ once (Map.toList namedArginfo')

                  -- What happens now depends on satisfying the positional
                  -- parameters.
                  if nargs < nparams then do
                      -- Partial application. Result is still a function type.
                      -- Keep the named parameters we we didn't find values for.
                      -- If there are any named arguments we didn't match to
                      -- parameters, that's an error.
                      -- Stick [] in the namelist field because we're downstream
                      -- of the only thing that uses it.
                      objectToLeftoverArgs
                      let params' = drop nargs params
                      pure $ TyFunc typos noNames params' namedParams' ret

                  else if nargs == nparams then do
                      -- Complete application, result is the return type.
                      -- If there are leftover named arguments, that's an
                      -- error.
                      -- No more named arguments can be applied.
                      objectToLeftoverArgs
                      pure ret

                  else do
                      -- There are args left. Check another call against
                      -- the return type. Pass on any leftover named args.
                      -- Any unused named parameters are left unapplied;
                      -- that is not an error.
                      let arginfo' = (drop nparams arginfo)
                      checkCall False origTy ret arginfo' namedArginfo'

              TyUnifyVar{} -> do
                  -- We don't have a function type yet. Generate a
                  -- function type of the right arity and stuff the
                  -- argument types we've got into it. (In principle
                  -- maybe we ought to generate N fresh tyvars and unify
                  -- them with the args, but that serves no purpose.)
                  --
                  -- The position we want to use for this is not the
                  -- position of the whole call (that's confusing if
                  -- we're a second or subsequent iteration of
                  -- checkCall) but the span of the positions of the
                  -- remaining args.
                  --
                  -- Note: we put [] in the namelist field because we're
                  -- downstream of the only thing that uses it.
                  --
                  let callpos =
                        let ps1 = map (\(arg, _ty) -> Pos.getPos arg) arginfo
                            ps2 =
                              let once (_name, (namepos, arg, _ty)) =
                                    Pos.spanPos namepos (Pos.getPos arg)
                              in
                              map once (Map.toList namedArginfo)
                        in
                        Pos.maxSpan (ps1 ++ ps2)

                  let callpos' = PosInferred InfContext callpos
                      (_args, argtys) = unzip arginfo
                      namedArgtys = Map.map (\(_namepos, _arg, argty) -> argty) namedArginfo
                  ret <- getFreshTyVar callpos'
                  let ty' = TyFunc callpos' noNames argtys namedArgtys ret
                  -- Unify the tyvar we got with the function type
                  unify ty callpos ty'
                  -- Hand back the return type
                  pure ret
              _ -> do
                  -- Not a function.
                  ppopts <- asks tiPPOpts
                  -- extract the position of the first excess argument
                  let argpos = case arginfo of
                        (arg, _) : _ -> Pos.getPos arg
                        [] -> case Map.toList namedArginfo of
                            (_, (_, arg, _)) : _ ->
                                Pos.getPos arg
                            [] -> panic "checkExpr / Application" [
                                "Call with empty arg list"
                             ]
                  if isFirst then do
                      -- The value we got didn't accept any arguments at
                      -- all, so use the position of the function value
                      -- to complain that it isn't a function.
                      let ty' = prettyType ppopts ty
                      let nNamed = length (Map.toList namedArginfo)
                          nargs' = case length arginfo + nNamed of
                            1 -> "one argument"
                            n -> PP.viaShow n <+> "arguments"
                      recordError (Pos.getPos f) $ "This expression is not" <+>
                                                   "a function (type is" <+>
                                                   ty' <> ")"
                      recordError pos $ "but is applied here to" <+>
                                        nargs' <> "."
                      recordError' $ prettyTypeDetails ppopts ty
                  else do
                      -- We already absorbed some arguments so we have
                      -- too many arguments rather than a non-function.
                      -- Use the position of the first excess argument
                      -- to complain.
                      let origTy' = prettyType ppopts origTy
                          -- Abuse the prettyprinter to keep it from
                          -- inserting extra unwanted line
                          -- breaks. Compare the code in
                          -- `prettyTypeDetails`.  XXX.
                          origTy'' =
                            case Text.lines $ PPS.renderText ppopts origTy' of
                                [t] -> PP.pretty t
                                ts -> PP.nest 3 $ PP.vsep $ map PP.pretty ts
                      recordError argpos $ "Too many arguments to function" <+>
                                           "of type" <+> origTy''
                      recordError' $ prettyTypeDetails ppopts origTy
                  let trailing = Pos.trailingPos argpos
                      leading = Pos.leadingPos pos
                  when (Pos.differentLines trailing leading) $
                      recordError argpos "Did you forget a semicolon?"
                  -- Return a fresh tyvar as an error placeholder.
                  getFreshTyVar pos

        (f', ty'f) <- inferExpr f
        ty'f' <- expandFully (Pos.getPos f) ty'f

        let oneArg (mbName, a) = do
              (a', ty'a) <- inferExpr a
              pure (mbName, a', ty'a)
        arginfo <- mapM oneArg args0

        -- Divide off the named arguments
        (arginfo', namedArginfo') <- do
            let once (pa, na) (mbName, arg, ty) =
                  case mbName of
                      Nothing ->
                          pure ((arg, ty) : pa, na)
                      Just (namepos, name) ->
                          case Map.lookup name na of
                              Nothing -> do
                                  let na' = Map.insert name (namepos, arg, ty) na
                                  pure (pa, na')
                              Just _ -> do
                                  -- maybe we should have this check
                                  -- upstream like lambdas do...
                                  recordError namepos $ "Duplicate named" <+>
                                                        "argument" <+>
                                                        PP.pretty name
                                  pure (pa, na)
            (pa, na) <- foldM once ([], Map.empty) arginfo
            -- Because foldM is a foldl, we need to reverse pa
            pure (reverse pa, na)

        ty'result <- checkCall True ty'f' ty'f' arginfo' namedArginfo'

        let args' = map (\(arg, _ty) -> (Nothing, arg)) arginfo'
        let namedArgs' =
              let once (name, (namepos, arg, _ty)) =
                    (Just (namepos, name), arg)
              in
              map once $ Map.toList namedArginfo'
        return (Application pos f' (args' ++ namedArgs'), ty'result)

    Let pos dg body -> do
        dg' <- inferDeclGroup ReadOnlyVar dg
        pushScope
        addDeclGroup ReadOnlyVar dg'
        (body', ty) <- inferExpr body
        popScope
        let e' = Let pos dg' body'
        return (e', ty)

    TSig _pos e t -> do
        t' <- checkType kindStar t
        (e',t'') <- inferExpr e
        unify t' (Pos.getPos e') t''
        return (e',t'')

    IfThenElse pos e1 e2 e3 -> do
        e1' <- checkExpr e1 (tBool (PosInferred InfContext $ Pos.getPos e1))
        (e2', t) <- inferExpr e2
        e3' <- checkExpr e3 t
        return (IfThenElse pos e1' e2' e3', t)

-- | Check the type of an expr, by inferring and then unifying the
--   result.
--
checkExpr :: Expr -> Type -> TI OutExpr
checkExpr e t = do
    (e', t') <- inferExpr e
    unify t (Pos.getPos e') t'
    return e'

--
-- patterns
--

-- | Infer types for a pattern, producing fresh type variables as needed.
--
--   There may already be types in the pattern if there were explicit
--   type annotations in the input; if so don't throw them away.
--
--   If the enclosing context says "rebindable", either
--      - the variable is not already present in the environment
--      - or it is present and already declared "rebindable", in which
--        case it must have the same type.
inferPattern :: Rebindable -> Pattern -> TI (Type, Pattern)
inferPattern rebindable pat = do
    let resolveType pos mt = case mt of
          Nothing -> getFreshTyVar pos
          Just t -> checkType kindStar t

    case pat of
        PWild pos mt -> do
            t <- resolveType pos mt
            return (t, PWild pos (Just t))
        PVar allpos xpos x mt -> do
            t <- resolveType allpos mt
            env <- gets tiVarEnv
            case ScopedMap.lookup x env of
                Nothing -> pure ()
                Just (prevpos, lc, prevrb, tyscheme) -> case rebindable of
                    RebindableVar -> do
                        let croak msg =
                              recordError xpos $ "Cannot rebind" <+>
                                                 PP.pretty x <>
                                                 ":" <+> msg
                        avail <- asks tiPrimsAvail
                        when (not $ Set.member lc avail) $
                            croak "A previous binding exists but is hidden"
                        oldt <- case tyscheme of
                            Forall [] oldt' -> pure oldt'
                            Forall (_ : _) _ -> do
                                croak "Polymorphic objects cannot be rebound"
                                getErrorTyVar xpos
                        when (prevrb == ReadOnlyVar) $
                            croak "Previous binding was not tagged 'rebindable'"
                        unify oldt prevpos t
                    ReadOnlyVar -> do
                        -- The ocaml-style behavior of being able to do
                        --    let x = 3;
                        --    let x = foo x;
                        --    let x = bar x;
                        -- to create successive versions of x is often
                        -- convenient, and an unconditional
                        -- warning defeats that. However, the historical
                        -- behavior of SAWScript (in certain contexts)
                        -- is to mutate x, such that
                        --     let x = 3;
                        --     let y = x;
                        --     let x = 4;
                        --     print y;
                        -- would print 4. Therefore, we warn aggressively
                        -- in case anyone was relying on the old
                        -- behavior.
                        --
                        -- FUTURE: we currently can't identify the scopes
                        -- that are involved; in the future we might want
                        -- to (a) issue this warning only for rebinds at
                        -- the syntactic top level, and (b) have a
                        -- different warning for locals that shadow
                        -- variables from outer scopes.
                        recordWarning xpos $ "Redeclaration of" <+> PP.pretty x
                        recordWarning prevpos $ "Previous declaration was here"
            return (t, PVar allpos xpos x (Just t))
        PTuple pos ps -> do
            (ts, ps') <- unzip <$> mapM (inferPattern rebindable) ps
            return (tTuple (PosInferred InfTerm pos) ts, PTuple pos ps')

-- | Check the type of a pattern, by inferring and then unifying the
--   result.
checkPattern :: Rebindable -> Type -> Pattern -> TI Pattern
checkPattern rebindable t pat = do
    (pt, pat') <- inferPattern rebindable pat
    unify t (Pos.getPos pat) pt
    return pat'

--
-- statements
--

-- | Add a typedef binding to the type environment.
--
-- The expansion (t) has been checked, so it's ok to panic if it
-- refers to something not visible in the environment.
addTypedef :: Name -> Type -> TI ()
addTypedef a ty = do
    avail <- asks tiPrimsAvail
    env <- gets tiTyEnv
    let ty' = Util.substituteTyVars avail env ty
        env' = ScopedMap.insert a (Current, ConcreteType ty') env
    modify (\rw -> rw { tiTyEnv = env' })

-- | Break a monadic type down into its monad and value types, if it is one.
--
--      monadType (TopLevel Int) gives Just (TopLevel, Int)
--      monadType Int gives Nothing
--
monadType :: Type -> Maybe (Type, Type)
monadType ty = case ty of
  TyCon _ BlockCon [ctx@(TyCon _ (ContextCon _) []), valty] ->
      Just (ctx, valty)
  TyCon _ BlockCon [ctx@(TyVar _ name), valty] | isMonad name ->
      Just (ctx, valty)
  -- We don't currently ever generate these types, but be future-proof
  TyCon pos (ContextCon ctx) [valty] ->
      Just (TyCon pos (ContextCon ctx) [], valty)
  -- and this one can't even be represented yet
--TyVar pos name [valty] | isMonad name ->
--    Just (TyVar pos name, valty)
  _ ->
      Nothing
  where
    -- Baking in these strings is untidy. I'd worry more about it if
    -- this code were being used for real rather than as part of a
    -- temporary accomodation for compatibility purposes.
    isMonad "LLVMSetup" = True
    isMonad "JVMSetup" = True
    isMonad "MIRSetup" = True
    isMonad _ = False

-- | Wrap an expression in @return@
wrapReturn :: Expr -> Expr
wrapReturn e =
    let ePos = Pos.getPos e
        retPos = PosInternal "<implicitly inserted return>"
        ret = Var retPos "return"
    in
    Application ePos ret [(Nothing, e)]

-- | Type inference for a single statement.
--
--   The boolean is whether we're at the syntactic top level, which is used
--   for workaround logic for issue #2162.
--
--   The passed-in position should be the position associated with the monad type
--   the first type argument (ctx) is the monad type for any binds that occur.
--
-- Updates the environment and returns an updated statement.
inferStmt :: Bool -> Pos -> Type -> Stmt -> TI Stmt
inferStmt atSyntacticTopLevel blockpos ctx s = do
    ppopts <- asks tiPPOpts
    case s of
        StmtBind spos pat e -> do
            (pty, pat') <- inferPattern ReadOnlyVar pat
            -- The expression should be of monad type. The
            -- straightforward way to proceed here is to unify both
            -- the monad type (ctx) and the result type expected by
            -- the pattern (pty), like this:
            --    e' <- checkExpr e (tBlock blockpos ctx pty)
            --
            -- However, historically when at the syntactic top level
            -- (only), the monad type was left off, meaning that
            -- various incorrect forms were silently accepted. Fixing
            -- this in Dec 2024 triggered a lot of fallout, so we want
            -- to specifically check for the following cases. (Again,
            -- only when at the syntactic top level. Which is not when
            -- in the TopLevel monad.)
            --    x <- e for non-monadic e
            --    x <- e for e in the wrong monad
            --
            -- These are now errors again, but the explicit messages
            -- should be kept for at least one further release. See
            -- #2167 and #2162. They are warnings in SAW 1.5; they
            -- will be errors in 1.6; they can be removed in 1.7.
            --
            -- To accomplish this, call inferExpr to get a type for
            -- the expression, and examine it. If the special cases
            -- apply, issue special-case errors with explanations,
            -- unify the type with only the pattern type, and patch up
            -- the expression by wrapping it in "return".  (The latter
            -- will restore the old behavior for both cases, so we
            -- don't need to also gunk up the interpreter to handle
            -- this problem.)
            --
            -- If the special cases don't apply, unify the result type
            -- with the complete type.
            (e', ty) <- inferExpr e
            ty' <- expandFully (Pos.getPos e) ty

            -- The correct, restricted case
            let restrictToCorrect = do
                  -- unify the type of e with the expected monad and
                  -- pattern types
                  unify (tBlock blockpos ctx pty) (Pos.getPos e') ty
                  return e'

            -- The special case for non-monadic values
            let allowNonMonadic = do
                  recordError spos $ "Monadic bind of non-monadic value;" <+>
                                     "rewrite as let-binding or use return"
                  unify pty (Pos.getPos e') ty
                  -- Wrap the expression in "return" to correct the type
                  return $ wrapReturn e'

            -- The special case for the wrong monad
            let allowWrongMonad ctx' valty' = do
                  let pctx =  prettyType ppopts ctx
                      pctx' = prettyType ppopts ctx'
                  recordError spos $ "Monadic bind with the wrong monad;" <+>
                                     "found" <+> pctx' <+>
                                     "but expected" <+> pctx
                  recordError spos $ "This creates the action but does" <+>
                                     "not execute it; if you meant to do" <+>
                                     "that, prefix the" <+>
                                     "expression with return"

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
                  unify pty (Pos.getPos e') (tBlock spos ctx' valty')

                  -- Wrap the expression in "return" to produce an
                  -- expression of type TopLevel (m t).
                  return $ wrapReturn e'

            -- Figure out which case applies.
            e'' <-
                if not atSyntacticTopLevel then
                    restrictToCorrect
                else do
                    ok <- matches blockpos (tBlock blockpos ctx pty) ty
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
            addPattern pat'
            return s'
        StmtLet spos rebindable dg -> do
            when (rebindable == RebindableVar && not atSyntacticTopLevel) $ do
                recordError spos "Invalid use of 'rebindable'"
                recordError spos "It is only allowed at the syntactic top level"
            dg' <- inferDeclGroup rebindable dg
            let s' = StmtLet spos rebindable dg'
            addDeclGroup rebindable dg'
            return s'
        StmtCode _allpos _spos _txt ->
            return s
        StmtImport _spos _ ->
            return s
        StmtInclude spos _ _ -> do
            -- Restrict include to TopLevel. This matches the prior
            -- behavior when it was a builtin function rather than
            -- syntax. FUTURE: consider relaxing the requirement.
            let spos' = PosInferred InfTerm spos
            let tm = TyCon spos' (ContextCon TopLevel) []
            tx <- getFreshTyVar spos
            unify (tBlock blockpos ctx tx) spos (tBlock spos tm tx)
            return s
        StmtTypedef allpos apos a ty -> do
            ty' <- checkType kindStar ty
            tyenv <- gets tiTyEnv
            case ScopedMap.lookup a tyenv of
                Nothing -> do
                    let s' = StmtTypedef allpos apos a ty'
                    addTypedef a ty'
                    return s'
                Just (lc, _expansion) -> do
                    -- Prohibit redefining any type, even ones that
                    -- aren't visible. In principle it is ok to
                    -- redefine a type that isn't visible, since
                    -- existing references to it shouldn't be visible
                    -- either. But (a) that's not always true, there
                    -- have been bugs in the builtin list before; and
                    -- (b) it would require remembering permanently
                    -- that any corresponding future use of
                    -- enable_experimental or enable_deprecated must
                    -- be blocked.
                    let a' = PP.pretty a
                    avail <- asks tiPrimsAvail
                    let addendum =
                          if Set.member lc avail then ""
                          else " (which is not currently visible)"
                    recordError allpos $ "Redefinition of type" <+> a' <>
                                         addendum
                    -- FUTURE: print the position of the previous definition
                    -- (currently we don't keep it around)
                    return s
        StmtPushdir _spos _ ->
            return s
        StmtPopdir _spos ->
            return s

-- | Inference for a do-block.
--
--   The passed-in position should be the position for the whole
--   statement block.
--
--   The first type argument (ctx) is the monad type for the block.
--
--   The second type argument (ty) is the expected full result type for
--   the block (including the monad) to be unified with the result type
--   found.
--
inferBlock :: Pos -> Type -> Type -> ([Stmt], Expr) -> TI ([OutStmt], OutExpr)
inferBlock blockpos ctx ty (stmts, lastexpr) = do
    let atSyntacticTopLevel = False

    -- Check the statements in order, left first.
    stmts' <- mapM (inferStmt atSyntacticTopLevel blockpos ctx) stmts

    -- Check the final expression.
    -- This produces the result type for the block.
    (lastexpr', ty') <- inferExpr lastexpr
    unify ty (Pos.getPos lastexpr) ty'

    return (stmts', lastexpr')

-- | Wrapper around inferStmt suitable for checking one statement at a
--   time. This is temporary scaffolding for the interpreter while
--   fixing it. (Currently the interpreter typechecks one statement at a
--   time when executing, even when not at the repl, and this involves
--   assorted messiness and technical debt. Eventually we'll get it into
--   a state where we can always just typecheck immediately after
--   parsing (including incrementally from the repl) but we're some
--   distance from that.) In the meantime the first step is to get it to
--   typecheck one statement at a time without special-casing any of
--   them, and this is how it does that.
--
--   Run inferStmt and then apply the current substitution before
--   returning the updated statement. Note that currently the caller
--   will throw away the updated environment; the interpreter has its
--   own misbegotten logic for handling that in its own way. (Which
--   should be removed.)
inferSingleStmt :: Pos -> Type -> Stmt -> TI Stmt
inferSingleStmt pos ctx s = do
    -- currently we are always at the syntactic top level here because
    -- that's how the interpreter works
    let atSyntacticTopLevel = True
    s' <- inferStmt atSyntacticTopLevel pos ctx s
    s'' <- applyCurrentSubst s'
    return s''

--
-- decls
--

-- | Create a type schema for a list of mutually referential
--   declarations out of their free vars.
--
--   (This creates names for any remaining unification vars, so
--   potentially updates the expression.)
--
--   The "foralls" argument is a set of tyvars that were mentioned
--   explicitly and should be forall-bound.
generalize ::
    Map Name Pos -> [Pattern] -> [OutExpr] -> [Type] ->
    TI [(Pattern, OutExpr, Schema)]
generalize foralls pats0 es0 ts0 = do
    -- first, substitute away any resolved unification variables
    -- in both the expressions and types.
    pats <- applyCurrentSubst pats0
    es <- applyCurrentSubst es0
    ts <- applyCurrentSubst ts0

    -- Extract lists of any unification vars and named type vars that
    -- still appear.
    let is0 = unifyVars ts
    let bs0 = Util.namedTyVars ts

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
    let is1 = is0 Map.\\ envUnifyVars
    let bs1 = Map.union foralls $ Map.withoutKeys bs0 knownNamedVars

    -- convert to lists
    let is2 = Map.toList is1
    let bs2 = Map.toList bs1

    -- if the position is "fresh" turn it into "inferred from term"
    let adjustPos pos = case pos of
          PosInferred InfFresh pos' -> PosInferred InfTerm pos'
          _ -> pos

    -- generate names for the unification vars
    let is3 = [ (i, adjustPos pos, "a." <> Text.pack (show i)) | (i, pos) <- is2 ]

    -- build a substitution
    let s = Map.fromList [ (i, TyVar pos n) | (i, pos, n) <- is3 ]

    -- get the names for the Forall
    let inames = [ (pos, n) | (_i, pos, n) <- is3 ]
    let bnames = [ (pos, x) | (x, pos) <- bs2 ]

    let mk pat e t =
          let pat' = appSubst s pat
              e' = appSubst s e
              t' = appSubst s t
          in
          (pat', e', Forall (inames ++ bnames) t')

    return $ zipWith3 mk pats es ts


-- | Check that a type is a function and isn't a plain value, in order
--   to reject recursive values in "rec" definitions. Otherwise they
--   crash the interpreter downstream. See issue #2203.
--
--   There are cases where it might be convenient to include a plain
--   value within a system of recursive declarations. For example, if
--   you have something like
--      rec foo x = ...
--      and foo0 = foo 0
--      and foo1 = foo 1
--      and bar x = ...
--      and bar0 = bar 0
--      and bar1 = bar 1
--      and baz x = ...
--      and baz0 = baz 0
--      and baz1 = baz 1
--   then depending on what the code is, it might be logically
--   reasonable to place the values like this and ugly to need to move
--   them out of the flow. If this ever comes up it might make sense to
--   loosen this check (e.g. to check whether the value is actually
--   recursive) and also fix the interpreter to not choke. However,
--   provided the values actually aren't recursive it is _possible_ to
--   move them out, so this is only worth chasing after given a fairly
--   compelling use case.
--
--   Note that actual recursively defined values are always bottom (in
--   the absence of mutable variables) and are best not allowed.
--
requireFunction :: Pos -> Type -> TI ()
requireFunction pos ty = do
    ty' <- expandFully pos ty
    case ty' of
        TyFunc _pos _ninfo _params _namedParams _ret ->
            return ()
        _ ->
            recordError pos $ "Only functions may be recursive."

-- | Type inference for a declaration.
--
--   Note that the type schema slot in Decl is always Nothing the way it
--   comes from the parser; if there's an explicit type annotation on
--   the declaration, it shows up as a type signature in the expression.
--
--   This function does _not_ update the variable environment to reflect
--   the declaration. The caller does that. XXX: this seems messy. (But
--   note that checkDecl is used by the :type REPL command, which
--   shouldn't update anything, so it's not open and shut.)
inferDecl :: Rebindable -> Decl -> TI Decl
inferDecl rebindable d@(Decl pos pat _ e) = do
    -- collect the free type variables
    foralls <- inspectDeclFTVs d
    let foralls' = Map.map (\(typos, _kind) -> typos) foralls

    -- Add abstract type variables for the foralls while we check the body.
    -- Note: this is a variable declaration. It doesn't add types; the types
    -- get forall-bound in the type scheme by the `generalize` call.
    pushScope
    addAbstractTyVars foralls

    -- Check the body and check the pattern against the body.
    (e', t) <- inferExpr e
    pat' <- checkPattern rebindable t pat

    -- Use `generalize` to build the type scheme.
    ~[(pat'', e1, s)] <- generalize foralls' [pat'] [e'] [t]

    -- Drop the abstract type variables
    popScope

    -- Return the updated `Decl`
    return (Decl pos pat'' (Just s) e1)

-- | Type inference for a system of mutually recursive declarations.
--
--   Note that the type schema slot in the Decls is always Nothing as we
--   get them from the parser; if there's an explicit type annotation on
--   some or all of the declarations those shows up as type signatures
--   in the expressions.
--
--   This function does _not_ update the variable environment to reflect
--   the declaration. The caller does that. XXX: this is messy.
inferRecDecls :: [Decl] -> TI [Decl]
inferRecDecls ds = do
    -- Get the patterns out of the decls.
    let pats = map dPat ds

    -- Collect the free type variables.
    foralls <- Map.unions <$> mapM inspectDeclFTVs ds
    let foralls' = Map.map (\(typos, _kind) -> typos) foralls

    -- Add abstract type variables for the foralls while we check the
    -- bodies.
    pushScope
    addAbstractTyVars foralls

    -- Check the patterns first to get types.
    (_ts, pats') <- unzip <$> mapM (inferPattern ReadOnlyVar) pats

    -- Check all the expressions in an environment that includes all
    -- the bound variables.
    --
    -- FUTURE: we only need a second nested scope here because we run
    -- all the patterns through checkPattern a second time; if we do
    -- that after the addPatterns, every declaration is a "duplicate"
    -- and things go plop. It seems there ought to be a better way of
    -- handling all this that doesn't require visiting the patterns
    -- twice.
    pushScope
    addPatterns pats'
    let checkOneExpr (Decl _pos _p _ e) = inferExpr e
    (es, tys) <- unzip <$> mapM checkOneExpr ds
    popScope

    -- Only functions can be recursive. Check each participant.
    zipWithM_ (\d ty -> requireFunction (Pos.getPos d) ty) ds tys

    -- pats' has already been checked once, which will have inserted
    -- unification vars for any missing types. Running it through
    -- again will have no further effect, so we can ignore the
    -- theoretically-updated-again patterns returned by checkPattern.
    sequence_ $ zipWith (checkPattern ReadOnlyVar) tys pats'

    -- Run generalize and get back a list of updated expressions and
    -- type schemes.
    patetys <- generalize foralls' pats' es tys

    -- Drop the abstract type variables.
    popScope

    -- Generate the updated declarations.
    let rebuild pos (pat, e1, ty) = Decl pos pat (Just ty) e1
        ds' = zipWith rebuild (map Pos.getPos ds) patetys

    return ds'

-- | Type inference for a decl group.
inferDeclGroup :: Rebindable -> DeclGroup -> TI DeclGroup
inferDeclGroup rebindable dg = case dg of
    NonRecursive d -> do
        d' <- inferDecl rebindable d
        return (NonRecursive d')
    Recursive ds -> do
        -- The parser doesn't accept "rec rebindable" so panic if it appears.
        when (rebindable == RebindableVar) $
            panic "inferDeclGroup" [
                "Found 'rebindable' on a 'rec' declaration"
            ]
        ds' <- inferRecDecls ds
        return (Recursive ds')

--
-- types
--

-- | Look up a type constructor (in our fixed environment of hardcoded
--   types) and return its params as a list of kinds.
lookupTyCon :: TyCon -> [Kind]
lookupTyCon tycon = case tycon of
    TupleCon n -> genericTake n (repeat kindStar)
    ArrayCon -> [kindStar]
    StringCon -> []
    TermCon -> []
    TypeCon -> []
    BoolCon -> []
    IntCon -> []
    BlockCon -> [kindStarToStar, kindStar]
    AIGCon -> []
    CFGCon -> []
    JVMSpecCon -> []
    LLVMSpecCon -> []
    MIRSpecCon -> []
    ContextCon _ctx -> [kindStar]

-- | Check a type for validity and also for having the
--   correct kinding.
checkType :: Kind -> Type -> TI Type
checkType kind ty = case ty of
    TyCon pos tycon args -> do
        ppopts <- asks tiPPOpts

        -- First, look up the constructor.
        let params = lookupTyCon tycon
        let nparams = genericLength params
            nargs = genericLength args
            argsleft = kindNumArgs kind

        if nargs > nparams then do
            -- XXX special case for BlockCon (remove along with BlockCon)
            let (nargs', nparams', tycon') =
                  case (tycon, args) of
                      (BlockCon, arg : _) ->
                          let ty' = prettyType ppopts arg in
                          (PP.viaShow $ nargs - 1, PP.viaShow $ nparams - 1, ty')
                      (_, _) ->
                          let ty' = prettyTyCon tycon in
                          (PP.viaShow nargs, PP.viaShow nparams, ty')

            recordError pos $ "Too many type arguments for type constructor" <+>
                              tycon' <> "; found" <+> nargs' <+>
                              "but expected only" <+> nparams'
            getErrorTyVar pos
        else if nargs + argsleft /= nparams then do
            let kind' = prettyKind kind
                kindExp' = prettyKind $ Kind (nparams - nargs)
            recordError pos $ "Kind mismatch: expected" <+> kind' <+>
                              "but found" <+> kindExp'
            getErrorTyVar pos
        else do
            -- note that this will ignore the extra params, and return
            -- a list of the same length as the args given
            args' <- zipWithM checkType params args
            return $ TyCon pos tycon args'

    TyFunc pos nameinfo params namedParams ret -> do
        if kind /= kindStar then do
            let kind' = prettyKind kind
                kindStar' = prettyKind kindStar
            recordError pos $ "Kind mismatch: expected" <+> kind' <+>
                              "but found" <+> kindStar'
            getErrorTyVar pos
        else do
            params' <- mapM (checkType kindStar) params
            namedParams' <- mapM (checkType kindStar) namedParams
            when (null params' && not (null namedParams')) $ do
                recordError pos $ "Functions may not have only named" <+>
                                  "parameters; add ()"
            ret' <- checkType kindStar ret
            return $ TyFunc pos nameinfo params' namedParams' ret'

    TyRecord pos fields -> do
        if kind /= kindStar then do
            let kind' = prettyKind kind
                kindStar' = prettyKind kindStar
            recordError pos $ "Kind mismatch: expected" <+> kind' <+>
                              "but found" <+> kindStar'
            getErrorTyVar pos
        else do
            -- Someone upstream had better have checked for duplicate
            -- field names because we can't once the fields are loaded
            -- into a map. (XXX: someone hasn't)
            fields' <- traverse (checkType kindStar) fields
            return $ TyRecord pos fields'

    TyVar pos x -> do
        avail <- asks tiPrimsAvail
        tyenv <- gets tiTyEnv
        case ScopedMap.lookup x tyenv of
            Nothing -> do
                recordError pos $ "Unbound type variable" <+> PP.pretty x
                getErrorTyVar pos
            Just (lc, ty')
              | Set.member lc avail -> do
                  when (Util.isDeprecated lc) $
                      recordWarning pos $ "Type is deprecated:" <+> PP.pretty x

                  -- For typedefs, which appear here as ConcreteType
                  -- expansions, assume ty' was checked when it was
                  -- entered.
                  --
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
                  -- Abstract types may have any kind, because some are
                  -- monads; we carry the kind around.
                  -- 
                  let kindFound = case ty' of
                        ConcreteType _ -> kindStar
                        AbstractType kf -> kf

                  if kind /= kindFound then do
                      let kind' = prettyKind kind
                          kindFound' = prettyKind kindFound
                      recordError pos $ "Kind mismatch: expected" <+> kind' <+>
                                       "but found" <+> kindFound'
                      getErrorTyVar pos
                  else
                      -- We do _not_ want to expand typedefs when checking,
                      -- so return the original TyVar.
                      return ty
              | otherwise -> do
                  let x' = PP.dquotes (PP.pretty x)
                  recordError pos $ "Inaccessible type:" <+> x'
                  let how = if lc == HideDeprecated then "deprecated"
                            else "experimental"
                      cmd = "`enable_" <> how <> "`"
                  recordError pos $ "This type is available only after" <+>
                                    "running" <+> cmd <> "."
                  t' <- getFreshTyVar pos
                  return t'

    TyUnifyVar _pos _ix ->
        -- for now at least we don't track the kinds of unification vars
        -- (types of mismatched kinds can't be the same types, so they
        -- won't ever unify, so the possible mischief is limited) and all
        -- possible unification var numbers are well formed, so we don't
        -- need to do anything.
        return ty


------------------------------------------------------------
-- External interface

-- | Check a single statement. (This is an external interface.)
--
--   The first two arguments are the starting variable and typedef
--   environments to use.
--
--   The third is a current position, and the fourth is the
--   context/monad type associated with the execution.
checkStmt ::
      PPS.Opts ->
      Set PrimitiveLifecycle ->
      VarEnv ->
      TyEnv ->
      Context ->
      Stmt ->
      Result Stmt
checkStmt ppopts avail env tenv ctx stmt =
    -- XXX: we shouldn't need this position here.
    -- The position is used for the following things:
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
    let pos = Pos.getPos stmt
        ctxtype = TyCon pos (ContextCon ctx) []
    in
    runTI ppopts avail env tenv (inferSingleStmt pos ctxtype stmt)

-- | Check a single declaration. (This is an external interface.)
--
--   The first two arguments are the starting variable and typedef
--   environments to use.
checkDecl ::
      PPS.Opts ->
      Set PrimitiveLifecycle ->
      VarEnv ->
      TyEnv ->
      Decl ->
      Result Decl
checkDecl ppopts avail env tenv decl =
    runTI ppopts avail env tenv (inferDecl ReadOnlyVar decl)

-- | Check a found type (first argument) against an expected type
--   (second argument) and return True if they can be unified.
--
--   Both types are schemes because that's what we need upstream.
--
--   (This is an external interface.)
typesMatch ::
      PPS.Opts ->
      Set PrimitiveLifecycle ->
      TyEnv ->
      Schema ->
      Schema ->
      Bool
typesMatch ppopts avail tenv schema'found schema'expected =
  let unpack (Forall as ty) = do
        -- Generate unification vars for all the forall-bindings
        let generate (pos'a, a) = do
              ty'a <- getFreshTyVar pos'a
              return (a, (Current, ConcreteType ty'a))
        substs <- mapM generate as
        -- Substitute them into the type
        let ty' = Util.substituteTyVars' avail (Map.fromList substs) ty
        return ty'
      match = do
        -- Unpack the schemas and check if they match
        ty'found <- unpack schema'found
        ty'expected <- unpack schema'expected
        matches (Pos.getPos ty'found) ty'found ty'expected
  in
  case runTI ppopts avail ScopedMap.empty tenv match of
      (Left _errors, _warnings) -> False        -- not actually reachable
      (Right b, _warnings) -> b                 -- return match success/failure

-- | Check a schema (type) as used when constructing the builtins
--   table. (This is an external interface.)
--
--   The first argument is the lifecycle context the type is being used
--   in. More on that below. The second is the typedef environment to
--   use. The third argument is the schema to check.
--
--   All types found should be of kind *.
--
--   Purely a validity check; there's no updates it can make to the
--   schema that are of use to the caller, on the assumption that the
--   caller doesn't want to do stuff with the schema before exiting on
--   errors, which it doesn't. Thus, return the original schema and not
--   one with the potentially updated type.
--
--   (Otherwise we'd need to rerun `generalize` to build a new schema,
--   and that's a headache and not worthwhile given that the result
--   isn't going to be used.)
--
--   Do however return the original schema and not unit to make sure
--   the code actually gets evaluated.
--
--   This is called for the types of objects that may themselves not be
--   visible, so rather than using the caller's set of visible lifecycle
--   states, construct the set based on the lifecycle state of the
--   declaration context. Deprecated objects can see equally or less
--   deprecated types; experimental objects can see experimental types;
--   everything can see current types.
--
checkSchema ::
      PPS.Opts ->
      PrimitiveLifecycle ->
      TyEnv ->
      Schema ->
      Result Schema
checkSchema ppopts contextLC tyenv schema = do
    let check = do
          let Forall tyvars ty = schema
          -- Generate unification vars for all the forall-bindings
          let generate (pos'a, a) = do
                ty'a <- getFreshTyVar pos'a
                return (a, (Current, ConcreteType ty'a))
          substs <- mapM generate tyvars
          -- Substitute them into the type
          let ty' = Util.substituteTyVars' everythingAvailable (Map.fromList substs) ty
          -- The only way checking can return an updated type is if
          -- there's also an error, so discard the type
          _ <- checkType kindStar ty'
          return schema

    let avail = Set.fromList $ case contextLC of
          Current -> [Current]
          WarnDeprecated -> [Current, WarnDeprecated]
          HideDeprecated -> [Current, WarnDeprecated, HideDeprecated, Experimental]
          Experimental -> [Current, Experimental]
    runTI ppopts avail ScopedMap.empty tyenv check

-- | Check a schema (type) pattern as used by :search. (This is an
--   external interface.)
--
--   The first two arguments are the starting variable and typedef
--   environments to use. The third argument is the pattern.
--
--   Returns a possibly updated pattern.
--
checkSchemaPattern ::
      Set PrimitiveLifecycle ->
      VarEnv ->
      TyEnv ->
      SchemaPattern ->
      Result SchemaPattern
checkSchemaPattern _avail _env _tenv pat =
    -- For the time being, do nothing -- we specifically don't want it
    -- to reject unbound/free type variables (see Search.hs for a
    -- discussion of why) or underapplied type constructors, so the
    -- only check in checkType that makes sense to apply is the one
    -- for _overapplied_ type constructors, and that is (a) not
    -- critical (an overapplied type constructor will never match
    -- anything valid) and (b) as noted in checkType not currently
    -- actually reasonable because of limitations in the concrete
    -- syntax. Point (b) will probably change eventually, so we want
    -- to keep this hook and keep knowledge of its internals private
    -- here even though for now it's a nop.
    (Right pat, [])


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
