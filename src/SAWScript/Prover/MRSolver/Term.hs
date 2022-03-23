{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}

{- |
Module      : SAWScript.Prover.MRSolver.Term
Copyright   : Galois, Inc. 2022
License     : BSD3
Maintainer  : westbrook@galois.com
Stability   : experimental
Portability : non-portable (language extensions)

This module defines the representation of terms used in Mr. Solver and various
utility functions for operating on terms and term representations. The main
datatype is 'NormComp', which represents the result of one step of monadic
normalization - see @Solver.hs@ for the description of this normalization.
-}

module SAWScript.Prover.MRSolver.Term where

import Data.String
import Data.IORef
import Control.Monad.Reader
import qualified Data.IntMap as IntMap
import GHC.Generics

import Prettyprinter

import Data.Map (Map)
import qualified Data.Map as Map

import Verifier.SAW.Term.Functor
import Verifier.SAW.Term.CtxTerm (MonadTerm(..))
import Verifier.SAW.Term.Pretty
import Verifier.SAW.SharedTerm
import Verifier.SAW.Recognizer hiding ((:*:))
import Verifier.SAW.Cryptol.Monadify


----------------------------------------------------------------------
-- * MR Solver Term Representation
----------------------------------------------------------------------

-- | A variable used by the MR solver
newtype MRVar = MRVar { unMRVar :: ExtCns Term } deriving (Eq, Show, Ord)

-- | Get the type of an 'MRVar'
mrVarType :: MRVar -> Term
mrVarType = ecType . unMRVar

-- | Print the string name of an 'MRVar'
showMRVar :: MRVar -> String
showMRVar = show . ppName . ecName . unMRVar

-- | A tuple or record projection of a 'Term'
data TermProj = TermProjTuple Int | TermProjRecord FieldName
              deriving (Eq, Ord, Show)

-- | Recognize a 'Term' as 0 or more projections
asProjAll :: Term -> (Term, [TermProj])
asProjAll (asRecordSelector -> Just ((asProjAll -> (t, projs)), fld)) =
  (t, TermProjRecord fld:projs)
asProjAll (asTupleSelector -> Just ((asProjAll -> (t, projs)), i)) =
  (t, TermProjTuple i : projs)
asProjAll t = (t, [])

-- | Names of functions to be used in computations, which are either names bound
-- by letrec to for recursive calls to fixed-points, existential variables, or
-- (possibly projections of) of global named constants
data FunName
  = LetRecName MRVar | EVarFunName MRVar | GlobalName GlobalDef [TermProj]
  deriving (Eq, Ord, Show)

-- | Recognize a 'Term' as (possibly a projection of) a global name
asTypedGlobalProj :: Recognizer Term (GlobalDef, [TermProj])
asTypedGlobalProj (asProjAll -> ((asTypedGlobalDef -> Just glob), projs)) =
  Just (glob, projs)
asTypedGlobalProj _ = Nothing

-- | Recognize a 'Term' as (possibly a projection of) a global name
asGlobalFunName :: Recognizer Term FunName
asGlobalFunName (asTypedGlobalProj -> Just (glob, projs)) =
  Just $ GlobalName glob projs
asGlobalFunName _ = Nothing

-- | Convert a 'FunName' to an unshared term, for printing
funNameTerm :: FunName -> Term
funNameTerm (LetRecName var) = Unshared $ FTermF $ ExtCns $ unMRVar var
funNameTerm (EVarFunName var) = Unshared $ FTermF $ ExtCns $ unMRVar var
funNameTerm (GlobalName gdef []) = globalDefTerm gdef
funNameTerm (GlobalName gdef (TermProjTuple i : projs)) =
  Unshared $ FTermF $ TupleSelector (funNameTerm (GlobalName gdef projs)) i
funNameTerm (GlobalName gdef (TermProjRecord fname:projs)) =
  Unshared $ FTermF $ RecordProj (funNameTerm (GlobalName gdef projs)) fname

-- | A term specifically known to be of type @sort i@ for some @i@
newtype Type = Type Term deriving (Generic, Show)

-- | A Haskell representation of a @CompM@ in "monadic normal form"
data NormComp
  = ReturnM Term -- ^ A term @returnM a x@
  | ErrorM Term -- ^ A term @errorM a str@
  | Ite Term Comp Comp -- ^ If-then-else computation
  | Either Type Type CompFun CompFun Term -- ^ A sum elimination
  | MaybeElim Type Comp CompFun Term -- ^ A maybe elimination
  | OrM Comp Comp -- ^ an @orM@ computation
  | ExistsM Type CompFun -- ^ an @existsM@ computation
  | ForallM Type CompFun -- ^ a @forallM@ computation
  | FunBind FunName [Term] CompFun
    -- ^ Bind a monadic function with @N@ arguments in an @a -> CompM b@ term
  deriving (Generic, Show)

-- | A computation function of type @a -> CompM b@ for some @a@ and @b@
data CompFun
     -- | An arbitrary term
  = CompFunTerm Term
    -- | A special case for the term @\ (x:a) -> returnM a x@
  | CompFunReturn
    -- | The monadic composition @f >=> g@
  | CompFunComp CompFun CompFun
  deriving (Generic, Show)

-- | Compose two 'CompFun's, simplifying if one is a 'CompFunReturn'
compFunComp :: CompFun -> CompFun -> CompFun
compFunComp CompFunReturn f = f
compFunComp f CompFunReturn = f
compFunComp f g = CompFunComp f g

-- | If a 'CompFun' contains an explicit lambda-abstraction, then return the
-- textual name bound by that lambda
compFunVarName :: CompFun -> Maybe LocalName
compFunVarName (CompFunTerm (asLambda -> Just (nm, _, _))) = Just nm
compFunVarName (CompFunComp f _) = compFunVarName f
compFunVarName _ = Nothing

-- | If a 'CompFun' contains an explicit lambda-abstraction, then return the
-- input type for it
compFunInputType :: CompFun -> Maybe Type
compFunInputType (CompFunTerm (asLambda -> Just (_, tp, _))) = Just $ Type tp
compFunInputType (CompFunComp f _) = compFunInputType f
compFunInputType _ = Nothing

-- | A computation of type @CompM a@ for some @a@
data Comp = CompTerm Term | CompBind Comp CompFun | CompReturn Term
          deriving (Generic, Show)

-- | Match a type as being of the form @CompM a@ for some @a@
asCompM :: Term -> Maybe Term
asCompM (asApp -> Just (isGlobalDef "Prelude.CompM" -> Just (), tp)) =
  return tp
asCompM _ = fail "not a CompM type!"

-- | Test if a type normalizes to a monadic function type of 0 or more arguments
isCompFunType :: SharedContext -> Term -> IO Bool
isCompFunType sc t = scWhnf sc t >>= \case
  (asPiList -> (_, asCompM -> Just _)) -> return True
  _ -> return False


----------------------------------------------------------------------
-- * Mr Solver Environments
----------------------------------------------------------------------

-- | An assumption that a named function refines some specification. This has
-- the form
--
-- > forall x1, ..., xn. F e1 ... ek |= m
--
-- for some universal context @x1:T1, .., xn:Tn@, some list of argument
-- expressions @ei@ over the universal @xj@ variables, and some right-hand side
-- computation expression @m@.
data FunAssump = FunAssump {
  -- | The uvars that were in scope when this assmption was created, in order
  -- from outermost to innermost; that is, the uvars as "seen from outside their
  -- scope", which is the reverse of the order of 'mrUVars', below
  fassumpCtx :: [(LocalName,Term)],
  -- | The argument expressions @e1, ..., en@ over the 'fassumpCtx' uvars
  fassumpArgs :: [Term],
  -- | The right-hand side upper bound @m@ over the 'fassumpCtx' uvars
  fassumpRHS :: NormComp
}

-- | A map from function names to function refinement assumptions over that
-- name
--
-- FIXME: this should probably be an 'IntMap' on the 'VarIndex' of globals
type FunAssumps = Map FunName FunAssump

-- | A global MR Solver environment
data MREnv = MREnv {
  -- | The set of function refinements to be assumed by to Mr. Solver (which
  -- have hopefully been proved previously...)
  mreFunAssumps :: FunAssumps
  }

-- | The empty 'MREnv'
emptyMREnv :: MREnv
emptyMREnv = MREnv { mreFunAssumps = Map.empty }

-- | Add a 'FunAssump' to a Mr Solver environment
mrEnvAddFunAssump :: FunName -> FunAssump -> MREnv -> MREnv
mrEnvAddFunAssump f fassump env =
  env { mreFunAssumps = Map.insert f fassump (mreFunAssumps env) }


----------------------------------------------------------------------
-- * Utility Functions for Transforming 'Term's
----------------------------------------------------------------------

-- | Transform the immediate subterms of a term using the supplied function
traverseSubterms :: MonadTerm m => (Term -> m Term) -> Term -> m Term
traverseSubterms f (unwrapTermF -> tf) = traverse f tf >>= mkTermF

-- | Build a recursive memoized function for tranforming 'Term's. Take in a
-- function @f@ that intuitively performs one step of the transformation and
-- allow it to recursively call the memoized function being defined by passing
-- it as the first argument to @f@.
memoFixTermFun :: MonadIO m => ((Term -> m a) -> Term -> m a) -> Term -> m a
memoFixTermFun f term_top =
  do table_ref <- liftIO $ newIORef IntMap.empty
     let go t@(STApp { stAppIndex = ix }) =
           liftIO (readIORef table_ref) >>= \table ->
           case IntMap.lookup ix table of
             Just ret -> return ret
             Nothing ->
               do ret <- f go t
                  liftIO $ modifyIORef' table_ref (IntMap.insert ix ret)
                  return ret
         go t = f go t
     go term_top


----------------------------------------------------------------------
-- * Lifting MR Solver Terms
----------------------------------------------------------------------

-- | A term-like object is one that supports lifting and substitution. This
-- class can be derived using @DeriveAnyClass@.
class TermLike a where
  liftTermLike :: MonadTerm m => DeBruijnIndex -> DeBruijnIndex -> a -> m a
  substTermLike :: MonadTerm m => DeBruijnIndex -> [Term] -> a -> m a

  -- Default instances for @DeriveAnyClass@
  default liftTermLike :: (Generic a, GTermLike (Rep a), MonadTerm m) =>
                          DeBruijnIndex -> DeBruijnIndex -> a -> m a
  liftTermLike n i = fmap to . gLiftTermLike n i . from
  default substTermLike :: (Generic a, GTermLike (Rep a), MonadTerm m) =>
                           DeBruijnIndex -> [Term] -> a -> m a
  substTermLike n i = fmap to . gSubstTermLike n i . from

-- | A generic version of 'TermLike' for @DeriveAnyClass@, based on:
-- https://hackage.haskell.org/package/base-4.16.0.0/docs/GHC-Generics.html#g:12
class GTermLike f where
  gLiftTermLike :: MonadTerm m => DeBruijnIndex -> DeBruijnIndex -> f p -> m (f p)
  gSubstTermLike :: MonadTerm m => DeBruijnIndex -> [Term] -> f p -> m (f p)

-- | 'TermLike' on empty types
instance GTermLike V1 where
  gLiftTermLike _ _ = \case {}
  gSubstTermLike _ _ = \case {}

-- | 'TermLike' on unary types
instance GTermLike U1 where
  gLiftTermLike _ _ U1 = return U1
  gSubstTermLike _ _ U1 = return U1

-- | 'TermLike' on sums
instance (GTermLike f, GTermLike g) => GTermLike (f :+: g) where
  gLiftTermLike n i (L1 a) = L1 <$> gLiftTermLike n i a
  gLiftTermLike n i (R1 b) = R1 <$> gLiftTermLike n i b
  gSubstTermLike n s (L1 a) = L1 <$> gSubstTermLike n s a
  gSubstTermLike n s (R1 b) = R1 <$> gSubstTermLike n s b

-- | 'TermLike' on products
instance (GTermLike f, GTermLike g) => GTermLike (f :*: g) where
  gLiftTermLike n i (a :*: b) = (:*:) <$> gLiftTermLike n i a <*> gLiftTermLike n i b
  gSubstTermLike n s (a :*: b) = (:*:) <$> gSubstTermLike n s a <*> gSubstTermLike n s b

-- | 'TermLike' on fields
instance TermLike a => GTermLike (K1 i a) where
  gLiftTermLike n i (K1 a) = K1 <$> liftTermLike n i a
  gSubstTermLike n i (K1 a) = K1 <$> substTermLike n i a

-- | 'GTermLike' ignores meta-information
instance GTermLike a => GTermLike (M1 i c a) where
  gLiftTermLike n i (M1 a) = M1 <$> gLiftTermLike n i a
  gSubstTermLike n i (M1 a) = M1 <$> gSubstTermLike n i a

deriving instance _ => TermLike (a,b)
deriving instance _ => TermLike (a,b,c)
deriving instance _ => TermLike (a,b,c,d)
deriving instance _ => TermLike (a,b,c,d,e)
deriving instance _ => TermLike (a,b,c,d,e,f)
deriving instance _ => TermLike (a,b,c,d,e,f,g)
deriving instance _ => TermLike [a]

instance TermLike Term where
  liftTermLike = liftTerm
  substTermLike = substTerm

instance TermLike FunName where
  liftTermLike _ _ = return
  substTermLike _ _ = return

deriving instance TermLike Type
deriving instance TermLike NormComp
deriving instance TermLike CompFun
deriving instance TermLike Comp


----------------------------------------------------------------------
-- * Pretty-Printing MR Solver Terms
----------------------------------------------------------------------

-- | The monad for pretty-printing in a context of SAW core variables
type PPInCtxM = Reader [LocalName]

-- | Pretty-print an object in a SAW core context and render to a 'String'
showInCtx :: PrettyInCtx a => [LocalName] -> a -> String
showInCtx ctx a =
  renderSawDoc defaultPPOpts $ runReader (prettyInCtx a) ctx

-- | Pretty-print an object in the empty SAW core context
ppInEmptyCtx :: PrettyInCtx a => a -> SawDoc
ppInEmptyCtx a = runReader (prettyInCtx a) []

-- | A generic function for pretty-printing an object in a SAW core context of
-- locally-bound names
class PrettyInCtx a where
  prettyInCtx :: a -> PPInCtxM SawDoc

instance PrettyInCtx Term where
  prettyInCtx t = flip (ppTermInCtx defaultPPOpts) t <$> ask

-- | Combine a list of pretty-printed documents like applications are combined
prettyAppList :: [PPInCtxM SawDoc] -> PPInCtxM SawDoc
prettyAppList = fmap (group . hang 2 . vsep) . sequence

-- | Pretty-print the application of a 'Term'
prettyTermApp :: Term -> [Term] -> PPInCtxM SawDoc
prettyTermApp f_top args =
  prettyInCtx $ foldl (\f arg -> Unshared $ App f arg) f_top args

-- | FIXME: move this helper function somewhere better...
ppCtx :: [(LocalName,Term)] -> SawDoc
ppCtx = helper [] where
  helper :: [LocalName] -> [(LocalName,Term)] -> SawDoc
  helper _ [] = ""
  helper ns ((n,tp):ctx) =
    let ns' = n:ns in
    ppTermInCtx defaultPPOpts ns' (Unshared $ LocalVar 0) <> ":" <>
    ppTermInCtx defaultPPOpts ns tp <> ", " <> helper ns' ctx

instance PrettyInCtx String where
  prettyInCtx str = return $ fromString str

instance PrettyInCtx SawDoc where
  prettyInCtx pp = return pp

instance PrettyInCtx Type where
  prettyInCtx (Type t) = prettyInCtx t

instance PrettyInCtx MRVar where
  prettyInCtx (MRVar ec) = return $ ppName $ ecName ec

instance PrettyInCtx [Term] where
  prettyInCtx xs = list <$> mapM prettyInCtx xs

instance PrettyInCtx TermProj where
  prettyInCtx (TermProjTuple i) = return (pretty '.' <> pretty i)
  prettyInCtx (TermProjRecord fld) = return (pretty '.' <> pretty fld)

instance PrettyInCtx FunName where
  prettyInCtx (LetRecName var) = prettyInCtx var
  prettyInCtx (EVarFunName var) = prettyInCtx var
  prettyInCtx (GlobalName g projs) =
    foldM (\pp proj -> (pp <>) <$> prettyInCtx proj) (ppName $
                                                      globalDefName g) projs

instance PrettyInCtx Comp where
  prettyInCtx (CompTerm t) = prettyInCtx t
  prettyInCtx (CompBind c f) =
    prettyAppList [prettyInCtx c, return ">>=", prettyInCtx f]
  prettyInCtx (CompReturn t) =
    prettyAppList [ return "returnM", return "_", parens <$> prettyInCtx t]

instance PrettyInCtx CompFun where
  prettyInCtx (CompFunTerm t) = prettyInCtx t
  prettyInCtx CompFunReturn = return "returnM"
  prettyInCtx (CompFunComp f g) =
    prettyAppList [prettyInCtx f, return ">=>", prettyInCtx g]

instance PrettyInCtx NormComp where
  prettyInCtx (ReturnM t) =
    prettyAppList [return "returnM", return "_", parens <$> prettyInCtx t]
  prettyInCtx (ErrorM str) =
    prettyAppList [return "errorM", return "_", parens <$> prettyInCtx str]
  prettyInCtx (Ite cond t1 t2) =
    prettyAppList [return "ite", return "_", parens <$> prettyInCtx cond,
                   parens <$> prettyInCtx t1, parens <$> prettyInCtx t2]
  prettyInCtx (Either ltp rtp f g eith) =
    prettyAppList [return "either",
                   parens <$> prettyInCtx ltp, parens <$> prettyInCtx rtp,
                   return (parens "CompM _"),
                   parens <$> prettyInCtx f, parens <$> prettyInCtx g,
                   parens <$> prettyInCtx eith]
  prettyInCtx (MaybeElim tp m f mayb) =
    prettyAppList [return "maybe", parens <$> prettyInCtx tp,
                   return (parens "CompM _"), parens <$> prettyInCtx m,
                   parens <$> prettyInCtx f, parens <$> prettyInCtx mayb]
  prettyInCtx (OrM t1 t2) =
    prettyAppList [return "orM", return "_",
                   parens <$> prettyInCtx t1, parens <$> prettyInCtx t2]
  prettyInCtx (ExistsM tp f) =
    prettyAppList [return "existsM", prettyInCtx tp, return "_",
                   parens <$> prettyInCtx f]
  prettyInCtx (ForallM tp f) =
    prettyAppList [return "forallM", prettyInCtx tp, return "_",
                   parens <$> prettyInCtx f]
  prettyInCtx (FunBind f args CompFunReturn) =
    prettyTermApp (funNameTerm f) args
  prettyInCtx (FunBind f [] k) =
    prettyAppList [prettyInCtx f, return ">>=", prettyInCtx k]
  prettyInCtx (FunBind f args k) =
    prettyAppList [parens <$> prettyTermApp (funNameTerm f) args,
                   return ">>=", prettyInCtx k]
