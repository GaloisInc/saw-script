{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

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

import Prettyprinter

import Verifier.SAW.Term.Functor
import Verifier.SAW.Term.CtxTerm (MonadTerm(..))
import Verifier.SAW.Term.Pretty
import Verifier.SAW.SharedTerm
import Verifier.SAW.Recognizer
import Verifier.SAW.Cryptol.Monadify


----------------------------------------------------------------------
-- * MR Solver Term Representation
----------------------------------------------------------------------

-- | A variable used by the MR solver
newtype MRVar = MRVar { unMRVar :: ExtCns Term } deriving (Eq, Show, Ord)

-- | Get the type of an 'MRVar'
mrVarType :: MRVar -> Term
mrVarType = ecType . unMRVar

-- | A tuple or record projection of a 'Term'
data TermProj = TermProjLeft | TermProjRight | TermProjRecord FieldName
              deriving (Eq, Ord, Show)

-- | Recognize a 'Term' as 0 or more projections
asProjAll :: Term -> (Term, [TermProj])
asProjAll (asRecordSelector -> Just ((asProjAll -> (t, projs)), fld)) =
  (t, TermProjRecord fld:projs)
asProjAll (asPairSelector -> Just ((asProjAll -> (t, projs)), isRight))
  | isRight = (t, TermProjRight:projs)
  | not isRight = (t, TermProjLeft:projs)
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

-- | A term specifically known to be of type @sort i@ for some @i@
newtype Type = Type Term deriving Show

-- | A Haskell representation of a @CompM@ in "monadic normal form"
data NormComp
  = ReturnM Term -- ^ A term @returnM a x@
  | ErrorM Term -- ^ A term @errorM a str@
  | Ite Term Comp Comp -- ^ If-then-else computation
  | Either CompFun CompFun Term -- ^ A sum elimination
  | MaybeElim Type Comp CompFun Term -- ^ A maybe elimination
  | OrM Comp Comp -- ^ an @orM@ computation
  | ExistsM Type CompFun -- ^ an @existsM@ computation
  | ForallM Type CompFun -- ^ a @forallM@ computation
  | FunBind FunName [Term] CompFun
    -- ^ Bind a monadic function with @N@ arguments in an @a -> CompM b@ term
  deriving Show

-- | A computation function of type @a -> CompM b@ for some @a@ and @b@
data CompFun
     -- | An arbitrary term
  = CompFunTerm Term
    -- | A special case for the term @\ (x:a) -> returnM a x@
  | CompFunReturn
    -- | The monadic composition @f >=> g@
  | CompFunComp CompFun CompFun
  deriving Show

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
          deriving Show

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

-- | A term-like object is one that supports lifting and substitution
class TermLike a where
  liftTermLike :: MonadTerm m => DeBruijnIndex -> DeBruijnIndex -> a -> m a
  substTermLike :: MonadTerm m => DeBruijnIndex -> [Term] -> a -> m a

instance (TermLike a, TermLike b) => TermLike (a,b) where
  liftTermLike n i (a,b) = (,) <$> liftTermLike n i a <*> liftTermLike n i b
  substTermLike n s (a,b) = (,) <$> substTermLike n s a <*> substTermLike n s b

instance TermLike a => TermLike [a] where
  liftTermLike n i l = mapM (liftTermLike n i) l
  substTermLike n s l = mapM (substTermLike n s) l

instance TermLike Term where
  liftTermLike = liftTerm
  substTermLike = substTerm

instance TermLike Type where
  liftTermLike n i (Type tp) = Type <$> liftTerm n i tp
  substTermLike n s (Type tp) = Type <$> substTerm n s tp

instance TermLike NormComp where
  liftTermLike n i (ReturnM t) = ReturnM <$> liftTermLike n i t
  liftTermLike n i (ErrorM str) = ErrorM <$> liftTermLike n i str
  liftTermLike n i (Ite cond t1 t2) =
    Ite <$> liftTermLike n i cond <*> liftTermLike n i t1 <*> liftTermLike n i t2
  liftTermLike n i (Either f g eith) =
    Either <$> liftTermLike n i f <*> liftTermLike n i g <*> liftTermLike n i eith
  liftTermLike n i (MaybeElim tp m f mayb) =
    MaybeElim <$> liftTermLike n i tp <*> liftTermLike n i m
              <*> liftTermLike n i f <*> liftTermLike n i mayb
  liftTermLike n i (OrM t1 t2) =
    OrM <$> liftTermLike n i t1 <*> liftTermLike n i t2
  liftTermLike n i (ExistsM tp f) =
    ExistsM <$> liftTermLike n i tp <*> liftTermLike n i f
  liftTermLike n i (ForallM tp f) =
    ForallM <$> liftTermLike n i tp <*> liftTermLike n i f
  liftTermLike n i (FunBind nm args f) =
    FunBind nm <$> mapM (liftTermLike n i) args <*> liftTermLike n i f

  substTermLike n s (ReturnM t) = ReturnM <$> substTermLike n s t
  substTermLike n s (ErrorM str) = ErrorM <$> substTermLike n s str
  substTermLike n s (Ite cond t1 t2) =
    Ite <$> substTermLike n s cond <*> substTermLike n s t1
    <*> substTermLike n s t2
  substTermLike n s (Either f g eith) =
    Either <$> substTermLike n s f <*> substTermLike n s g
    <*> substTermLike n s eith
  substTermLike n s (MaybeElim tp m f mayb) =
    MaybeElim <$> substTermLike n s tp <*> substTermLike n s m
              <*> substTermLike n s f <*> substTermLike n s mayb
  substTermLike n s (OrM t1 t2) =
    OrM <$> substTermLike n s t1 <*> substTermLike n s t2
  substTermLike n s (ExistsM tp f) =
    ExistsM <$> substTermLike n s tp <*> substTermLike n s f
  substTermLike n s (ForallM tp f) =
    ForallM <$> substTermLike n s tp <*> substTermLike n s f
  substTermLike n s (FunBind nm args f) =
    FunBind nm <$> mapM (substTermLike n s) args <*> substTermLike n s f

instance TermLike CompFun where
  liftTermLike n i (CompFunTerm t) = CompFunTerm <$> liftTermLike n i t
  liftTermLike _ _ CompFunReturn = return CompFunReturn
  liftTermLike n i (CompFunComp f g) =
    CompFunComp <$> liftTermLike n i f <*> liftTermLike n i g

  substTermLike n s (CompFunTerm t) = CompFunTerm <$> substTermLike n s t
  substTermLike _ _ CompFunReturn = return CompFunReturn
  substTermLike n s (CompFunComp f g) =
    CompFunComp <$> substTermLike n s f <*> substTermLike n s g

instance TermLike Comp where
  liftTermLike n i (CompTerm t) = CompTerm <$> liftTermLike n i t
  liftTermLike n i (CompBind m f) =
    CompBind <$> liftTermLike n i m <*> liftTermLike n i f
  liftTermLike n i (CompReturn t) = CompReturn <$> liftTermLike n i t
  substTermLike n s (CompTerm t) = CompTerm <$> substTermLike n s t
  substTermLike n s (CompBind m f) =
    CompBind <$> substTermLike n s m <*> substTermLike n s f
  substTermLike n s (CompReturn t) = CompReturn <$> substTermLike n s t


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

-- | Combine a list of pretty-printed documents that represent an application
prettyAppList :: [PPInCtxM SawDoc] -> PPInCtxM SawDoc
prettyAppList = fmap (group . hang 2 . vsep) . sequence

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

instance PrettyInCtx TermProj where
  prettyInCtx TermProjLeft = return (pretty '.' <> "1")
  prettyInCtx TermProjRight = return (pretty '.' <> "2")
  prettyInCtx (TermProjRecord fld) = return (pretty '.' <> pretty fld)

instance PrettyInCtx FunName where
  prettyInCtx (LetRecName var) = prettyInCtx var
  prettyInCtx (EVarFunName var) = prettyInCtx var
  prettyInCtx (GlobalName g projs) =
    foldM (\pp proj -> (pp <>) <$> prettyInCtx proj) (viaShow g) projs

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
  prettyInCtx (Either f g eith) =
    prettyAppList [return "either", return "_", return "_", return "_",
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
    prettyAppList (prettyInCtx f : map prettyInCtx args)
  prettyInCtx (FunBind f [] k) =
    prettyAppList [prettyInCtx f, return ">>=", prettyInCtx k]
  prettyInCtx (FunBind f args k) =
    prettyAppList
    [parens <$> prettyAppList (prettyInCtx f : map prettyInCtx args),
     return ">>=", prettyInCtx k]
