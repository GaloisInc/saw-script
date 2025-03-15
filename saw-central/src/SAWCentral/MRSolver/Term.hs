{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}

{- |
Module      : SAWCentral.MRSolver.Term
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

module SAWCentral.MRSolver.Term where

import Data.String
import Data.IORef
import Control.Monad (foldM)
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Reader (MonadReader(..), Reader, runReader)
import qualified Data.IntMap as IntMap
import Numeric.Natural (Natural)
import GHC.Generics

import Prettyprinter
import Data.Text (Text, unpack)

import SAWCore.Term.Functor
import SAWCore.Term.CtxTerm (MonadTerm(..))
import SAWCore.Term.Pretty
import SAWCore.SharedTerm
import SAWCore.Recognizer hiding ((:*:))
import CryptolSAWCore.Monadify


----------------------------------------------------------------------
-- * MR Solver Term Representation
----------------------------------------------------------------------

-- | Recognize a nested pi type with at least @N@ arguments, returning the
-- context of those first @N@ arguments and the body
asPiListN :: Int -> Recognizer Term ([(LocalName,Term)], Term)
asPiListN 0 tp = Just ([], tp)
asPiListN i (asPi -> Just (x, tp, body)) =
  fmap (\(ctx, body') -> ((x,tp):ctx, body')) $ asPiListN (i-1) body
asPiListN _ _ = Nothing

-- | A variable used by the MR solver
newtype MRVar = MRVar { unMRVar :: ExtCns Term } deriving (Eq, Show, Ord)

-- | Get the type of an 'MRVar'
mrVarType :: MRVar -> Term
mrVarType = ecType . unMRVar

-- | Print the string name of an 'MRVar'
showMRVar :: MRVar -> String
showMRVar = show . ppName . ecName . unMRVar

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
-- by @multiFixS@ for recursive calls to fixed-points, existential variables, or
-- (possibly projections of) of global named constants
data FunName
  = CallSName MRVar | EVarFunName MRVar | GlobalName GlobalDef [TermProj]
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
funNameTerm (CallSName var) = Unshared $ FTermF $ ExtCns $ unMRVar var
funNameTerm (EVarFunName var) = Unshared $ FTermF $ ExtCns $ unMRVar var
funNameTerm (GlobalName gdef []) = globalDefTerm gdef
funNameTerm (GlobalName gdef (TermProjLeft:projs)) =
  Unshared $ FTermF $ PairLeft $ funNameTerm (GlobalName gdef projs)
funNameTerm (GlobalName gdef (TermProjRight:projs)) =
  Unshared $ FTermF $ PairRight $ funNameTerm (GlobalName gdef projs)
funNameTerm (GlobalName gdef (TermProjRecord fname:projs)) =
  Unshared $ FTermF $ RecordProj (funNameTerm (GlobalName gdef projs)) fname

-- | A term specifically known to be of type @sort i@ for some @i@
newtype Type = Type { typeTm :: Term } deriving (Generic, Show)

-- | A context of variables, with names and types. To avoid confusion as to
-- how variables are ordered, do not use this type's constructor directly.
-- Instead, use the combinators defined below.
newtype MRVarCtx = MRVarCtx [(LocalName,Type)]
                   -- ^ Internally, we store these names and types in order
                   -- from innermost to outermost variable, see
                   -- 'mrVarCtxInnerToOuter'
                   deriving (Generic, Show)

-- | Build an empty context of variables
emptyMRVarCtx :: MRVarCtx
emptyMRVarCtx = MRVarCtx []

-- | Build a context with a single variable of the given name and type
singletonMRVarCtx :: LocalName -> Type -> MRVarCtx
singletonMRVarCtx nm tp = MRVarCtx [(nm,tp)]

-- | Add a context of new variables (the first argument) to an existing context
-- (the second argument). The new variables to add must be in the existing
-- context, i.e. all the types in the first argument must be in the context of
-- the second argument.
mrVarCtxAppend :: MRVarCtx -> MRVarCtx -> MRVarCtx
mrVarCtxAppend (MRVarCtx ctx1) (MRVarCtx ctx2) = MRVarCtx (ctx1 ++ ctx2)

-- | Return the number of variables in the given context
mrVarCtxLength :: MRVarCtx -> Int
mrVarCtxLength (MRVarCtx ctx) = length ctx

-- | Return a list of the names and types of the variables in the given
-- context in order from innermost to outermost, i.e., where element @i@
-- corresponds to deBruijn index @i@, and each type is in the context of
-- all the variables which come after it in the list (i.e. all the variables
-- which come after a type in the list are free in that type). In other words,
-- the list is ordered from newest to oldest variable.
mrVarCtxInnerToOuter :: MRVarCtx -> [(LocalName,Term)]
mrVarCtxInnerToOuter (MRVarCtx ctx) = map (\(nm, Type tp) -> (nm, tp)) ctx

-- | Build a context of variables from a list of names and types in innermost
-- to outermost order - see 'mrVarCtxInnerToOuter'.
mrVarCtxFromInnerToOuter :: [(LocalName,Term)] -> MRVarCtx
mrVarCtxFromInnerToOuter = MRVarCtx . map (\(nm,tp) -> (nm, Type tp))

-- | Return a list of the names and types of the variables in the given
-- context in order from outermost to innermost, i.e., where element @i@
-- corresponds to deBruijn index @len - i@, and each type is in the context of
-- all the variables which come before it in the list (i.e. all the variables
-- which come before a type in the list are free in that type). In other words,
-- the list is ordered from oldest to newest variable.
mrVarCtxOuterToInner :: MRVarCtx -> [(LocalName,Term)]
mrVarCtxOuterToInner = reverse . mrVarCtxInnerToOuter

-- | Build a context of variables from a list of names and types in outermost
-- to innermost order - see 'mrVarCtxOuterToInner'.
mrVarCtxFromOuterToInner :: [(LocalName,Term)] -> MRVarCtx
mrVarCtxFromOuterToInner = mrVarCtxFromInnerToOuter . reverse

-- | A Haskell representation of a @SpecM@ in \"monadic normal form\"
data NormComp
  = RetS Term -- ^ A term @retS _ _ a x@
  | ErrorS Term -- ^ A term @errorS _ _ a str@
  | Ite Term Comp Comp -- ^ If-then-else computation
  | Eithers [EitherElim] Term -- ^ A multi-way sum elimination
  | MaybeElim Type Comp CompFun Term -- ^ A maybe elimination
  | OrS Comp Comp -- ^ an @orS@ computation
  | AssertBoolBind Term CompFun -- ^ the bind of an @assertBoolS@ computation
  | AssumeBoolBind Term CompFun -- ^ the bind of an @assumeBoolS@ computation
  | ExistsBind Type CompFun -- ^ the bind of an @existsS@ computation
  | ForallBind Type CompFun -- ^ the bind of a @forallS@ computation
  | FunBind FunName [Term] CompFun
    -- ^ Bind a monadic function with @N@ arguments, possibly wrapped in a call
    -- to @liftStackS@, in an @a -> SpecM b@ term
  deriving (Generic, Show)

-- | An eliminator for an @Eithers@ type is a pair of the type of the disjunct
-- and a function from that type to the output type
type EitherElim = (Type,CompFun)

-- | A wrapper around 'Term' to designate it as a @SpecM@ event type
newtype EvTerm = EvTerm { unEvTerm :: Term } deriving (Generic, Show)

-- | A computation function of type @a -> SpecM b@ for some @a@ and @b@
data CompFun
     -- | An arbitrary term
  = CompFunTerm EvTerm Term
    -- | A special case for the term @\ (x:a) -> returnM a x@
  | CompFunReturn EvTerm Type
    -- | The monadic composition @f >=> g@
  | CompFunComp CompFun CompFun
  deriving (Generic, Show)

-- | Apply 'CompFunReturn' to a pair of an event type and a return type
mkCompFunReturn :: (EvTerm, Term) -> CompFun
mkCompFunReturn (ev, tp) = CompFunReturn ev $ Type tp

-- | Compose two 'CompFun's, simplifying if one is a 'CompFunReturn'
compFunComp :: CompFun -> CompFun -> CompFun
compFunComp (CompFunReturn _ _) f = f
compFunComp f (CompFunReturn _ _) = f
compFunComp f g = CompFunComp f g

-- | If a 'CompFun' contains an explicit lambda-abstraction, then return the
-- textual name bound by that lambda
compFunVarName :: CompFun -> Maybe LocalName
compFunVarName (CompFunTerm _ t) = asLambdaName t
compFunVarName (CompFunComp f _) = compFunVarName f
compFunVarName _ = Nothing

-- | If a 'CompFun' contains an explicit lambda-abstraction, then return the
-- input type for it
compFunInputType :: CompFun -> Maybe Type
compFunInputType (CompFunTerm _ (asLambda -> Just (_, tp, _))) = Just $ Type tp
compFunInputType (CompFunComp f _) = compFunInputType f
compFunInputType (CompFunReturn _ t) = Just t
compFunInputType _ = Nothing

-- | Get the @SpecM@ event type from a 'CompFun'
compFunEventType :: CompFun -> EvTerm
compFunEventType (CompFunTerm ev _) = ev
compFunEventType (CompFunReturn ev _) = ev
compFunEventType (CompFunComp f _) = compFunEventType f

-- | A computation of type @SpecM a@ for some @a@
data Comp = CompTerm Term | CompBind Comp CompFun | CompReturn Term
          deriving (Generic, Show)

-- | Match a type as being of the form @SpecM E a@ for some @E@ and @a@
asSpecM :: Term -> Maybe (EvTerm, Term)
asSpecM (asApplyAll -> (isGlobalDef "SpecM.SpecM" -> Just (), [ev, tp])) =
  return (EvTerm ev, tp)
asSpecM _ = fail "not a SpecM type, or event type is not closed!"

-- | Test if a type normalizes to a monadic function type of 0 or more arguments
isSpecFunType :: SharedContext -> Term -> IO Bool
isSpecFunType sc t = scWhnf sc t >>= \case
  (asPiList -> (_, asSpecM -> Just _)) -> return True
  _ -> return False


----------------------------------------------------------------------
-- * Useful 'Recognizer's for 'Term's
----------------------------------------------------------------------

-- | Recognize a 'Term' as an application of @bvToNat@ with a statically-known
-- natural number bit width
asBvToNatKnownW :: Recognizer Term (Natural, Term)
asBvToNatKnownW (asBvToNat -> Just (asNat -> Just n, t)) = Just (n, t)
asBvToNatKnownW _ = Nothing

-- | Recognize a term as a @Left@ or @Right@
asEither :: Recognizer Term (Either Term Term)
asEither (asCtor -> Just (c, [_, _, x]))
  | primName c == "Prelude.Left"  = return $ Left x
  | primName c == "Prelude.Right" = return $ Right x
asEither _ = Nothing

-- | Recognize the @Num@ type
asNumType :: Recognizer Term ()
asNumType (asDataType -> Just (primName -> "Cryptol.Num", _)) = Just ()
asNumType _ = Nothing

-- | Recognize a term as a @TCNum n@ or @TCInf@
asNum :: Recognizer Term (Either Term ())
asNum (asCtor -> Just (c, [n]))
  | primName c == "Cryptol.TCNum"  = return $ Left n
asNum (asCtor -> Just (c, []))
  | primName c == "Cryptol.TCInf"  = return $ Right ()
asNum _ = Nothing

-- | Recognize a term as being of the form @isFinite n@
asIsFinite :: Recognizer Term Term
asIsFinite (asApp -> Just (isGlobalDef "CryptolM.isFinite" -> Just (), n)) =
  Just n
asIsFinite _ = Nothing

-- | Recognize a term as being of the form @IsLtNat m n@
asIsLtNat :: Recognizer Term (Term, Term)
asIsLtNat (asApplyAll -> (isGlobalDef "Prelude.IsLtNat" -> Just (), [m, n])) =
  Just (m, n)
asIsLtNat _ = Nothing

-- | Recognize a bitvector type with a potentially symbolic length
asSymBitvectorType :: Recognizer Term Term
asSymBitvectorType (asVectorType -> Just (n, asBoolType -> Just ())) = Just n
asSymBitvectorType _ = Nothing

-- | Like 'asLambda', but only return's the lambda-bound variable's 'LocalName'
asLambdaName :: Recognizer Term LocalName
asLambdaName (asLambda -> Just (nm, _, _)) = Just nm
asLambdaName _ = Nothing


----------------------------------------------------------------------
-- * Utility Functions for Transforming 'Term's
----------------------------------------------------------------------

-- | Transform the immediate subterms of a term using the supplied function
traverseSubterms :: MonadTerm m => (Term -> m Term) -> Term -> m Term
traverseSubterms f (unwrapTermF -> tf) = traverse f tf >>= mkTermF

-- | Like 'memoFixTermFun', but threads through an accumulating argument
memoFixTermFunAccum :: MonadIO m =>
                       ((b -> Term -> m a) -> b -> Term -> m a) ->
                       b -> Term -> m a
memoFixTermFunAccum f acc_top term_top =
  do table_ref <- liftIO $ newIORef IntMap.empty
     let go acc t@(STApp { stAppIndex = ix }) =
           liftIO (readIORef table_ref) >>= \table ->
           case IntMap.lookup ix table of
             Just ret -> return ret
             Nothing ->
               do ret <- f go acc t
                  liftIO $ modifyIORef' table_ref (IntMap.insert ix ret)
                  return ret
         go acc t = f go acc t
     go acc_top term_top

-- | Build a recursive memoized function for tranforming 'Term's. Take in a
-- function @f@ that intuitively performs one step of the transformation and
-- allow it to recursively call the memoized function being defined by passing
-- it as the first argument to @f@.
memoFixTermFun :: MonadIO m => ((Term -> m a) -> Term -> m a) -> Term -> m a
memoFixTermFun f = memoFixTermFunAccum (f .) ()


----------------------------------------------------------------------
-- * Lifting MR Solver Terms
----------------------------------------------------------------------

-- | Apply 'liftTerm' to all component terms in a 'TermLike' object
liftTermLike :: (TermLike a, MonadTerm m) =>
                DeBruijnIndex -> DeBruijnIndex -> a -> m a
liftTermLike i n = mapTermLike (liftTerm i n)

-- | Apply 'substTerm' to all component terms in a 'TermLike' object
substTermLike :: (TermLike a, MonadTerm m) =>
                DeBruijnIndex -> [Term] -> a -> m a
substTermLike i s = mapTermLike (substTerm i s)

-- | A term-like object is one that supports monadically mapping over all
-- component terms. This is mainly used for lifting and substitution - see
-- @liftTermLike@ and @substTermLike@. This class can be derived using
-- @DeriveAnyClass@.
class TermLike a where
  mapTermLike :: MonadTerm m => (Term -> m Term) -> a -> m a

  -- Default instance for @DeriveAnyClass@
  default mapTermLike :: (Generic a, GTermLike (Rep a), MonadTerm m) =>
                         (Term -> m Term) -> a -> m a
  mapTermLike f = fmap to . gMapTermLike f . from

-- | A generic version of 'TermLike' for @DeriveAnyClass@, based on:
-- https://hackage.haskell.org/package/base-4.16.0.0/docs/GHC-Generics.html#g:12
class GTermLike f where
  gMapTermLike :: MonadTerm m => (Term -> m Term) -> f p -> m (f p)

-- | 'TermLike' on empty types
instance GTermLike V1 where
  gMapTermLike _ = \case {}

-- | 'TermLike' on unary types
instance GTermLike U1 where
  gMapTermLike _ U1 = return U1

-- | 'TermLike' on sums
instance (GTermLike f, GTermLike g) => GTermLike (f :+: g) where
  gMapTermLike f (L1 a) = L1 <$> gMapTermLike f a
  gMapTermLike f (R1 b) = R1 <$> gMapTermLike f b

-- | 'TermLike' on products
instance (GTermLike f, GTermLike g) => GTermLike (f :*: g) where
  gMapTermLike f (a :*: b) = (:*:) <$> gMapTermLike f a <*> gMapTermLike f b

-- | 'TermLike' on fields
instance TermLike a => GTermLike (K1 i a) where
  gMapTermLike f (K1 a) = K1 <$> mapTermLike f a

-- | 'GTermLike' ignores meta-information
instance GTermLike a => GTermLike (M1 i c a) where
  gMapTermLike f (M1 a) = M1 <$> gMapTermLike f a

deriving instance _ => TermLike (a,b)
deriving instance _ => TermLike (a,b,c)
deriving instance _ => TermLike (a,b,c,d)
deriving instance _ => TermLike (a,b,c,d,e)
deriving instance _ => TermLike (a,b,c,d,e,f)
deriving instance _ => TermLike (a,b,c,d,e,f,g)
-- NOTE: longer tuple types not supported by GHC 8.10
-- deriving instance _ => TermLike (a,b,c,d,e,f,g,i)
deriving instance _ => TermLike [a]
deriving instance TermLike ()

instance TermLike Term where
  mapTermLike f = f

instance TermLike FunName where
  mapTermLike _ = return
instance TermLike LocalName where
  mapTermLike _ = return
instance TermLike Natural where
  mapTermLike _ = return

deriving anyclass instance TermLike Type
deriving anyclass instance TermLike EvTerm
deriving instance TermLike NormComp
deriving instance TermLike CompFun
deriving instance TermLike Comp


----------------------------------------------------------------------
-- * Pretty-Printing MR Solver Terms
----------------------------------------------------------------------

-- | The monad for pretty-printing in a context of SAW core variables. The
-- context is in innermost-to-outermost order, i.e. from newest to oldest
-- variable (see 'mrVarCtxInnerToOuter' for more detail on this ordering).
-- 
-- NOTE: By convention, functions which return something of type 'PPInCtxM'
-- have the prefix @pretty@ (e.g. 'prettyInCtx', 'prettyTermApp') and
-- functions which return something of type 'SawDoc' have the prefix @pp@
-- (e.g. 'ppInCtx', 'ppTermAppInCtx'). This latter convention is consistent with
-- the rest of saw-script (e.g. 'ppTerm' defined in @SAWCore.Term.Pretty@,
-- 'ppFirstOrderValue' defined in @SAWCore.FiniteValue@).
newtype PPInCtxM a = PPInCtxM (Reader (PPOpts, [LocalName]) a)
                   deriving newtype (Functor, Applicative, Monad,
                                     MonadReader (PPOpts, [LocalName]))

-- | Locally set the context of SAW core variables for a 'PPInCtxM' computation
prettyWithCtx :: MRVarCtx -> PPInCtxM a -> PPInCtxM a
prettyWithCtx ctx = local (fmap $ const $ map fst $ mrVarCtxInnerToOuter ctx)

-- | Run a 'PPInCtxM' computation in the given 'MRVarCtx' context and 'PPOpts'
runPPInCtxM :: PPInCtxM a -> PPOpts -> MRVarCtx -> a
runPPInCtxM (PPInCtxM m) opts ctx =
  runReader m (opts, map fst $ mrVarCtxInnerToOuter ctx)

-- | Pretty-print an object in a SAW core context with the given 'PPOpts'
ppInCtx :: PrettyInCtx a => PPOpts -> MRVarCtx -> a -> SawDoc
ppInCtx opts ctx a = runPPInCtxM (prettyInCtx a) opts ctx

-- | Pretty-print an object in a SAW core context and render to a 'String' with
-- the given 'PPOpts'
showInCtx :: PrettyInCtx a => PPOpts -> MRVarCtx -> a -> String
showInCtx opts ctx a = renderSawDoc opts $ runPPInCtxM (prettyInCtx a) opts ctx

-- | A generic function for pretty-printing an object in a SAW core context of
-- locally-bound names
class PrettyInCtx a where
  prettyInCtx :: a -> PPInCtxM SawDoc

instance PrettyInCtx Term where
  prettyInCtx t = do (opts, ctx) <- ask
                     return $ ppTermInCtx opts ctx t

-- | Combine a list of pretty-printed documents like applications are combined
prettyAppList :: [PPInCtxM SawDoc] -> PPInCtxM SawDoc
prettyAppList = fmap (group . hang 2 . vsep) . sequence

-- | Pretty-print the application of a 'Term'
prettyTermApp :: Term -> [Term] -> PPInCtxM SawDoc
prettyTermApp f_top args =
  prettyInCtx $ foldl (\f arg -> Unshared $ App f arg) f_top args

-- | Pretty-print the application of a 'Term' in a SAW core context with the
-- given 'PPOpts'
ppTermAppInCtx :: PPOpts -> MRVarCtx -> Term -> [Term] -> SawDoc
ppTermAppInCtx opts ctx f_top args =
  runPPInCtxM (prettyTermApp f_top args) opts ctx

instance PrettyInCtx MRVarCtx where
  prettyInCtx ctx_top = do
    (opts, _) <- ask
    return $ align $ sep $ helper opts [] $ mrVarCtxOuterToInner ctx_top
    where helper :: PPOpts -> [LocalName] -> [(LocalName,Term)] -> [SawDoc]
          helper _ _ [] = []
          helper opts ns [(n, tp)] =
            [ppTermInCtx opts (n:ns) (Unshared $ LocalVar 0) <> ":" <>
             ppTermInCtx opts ns tp]
          helper opts ns ((n, tp):ctx) =
            (ppTermInCtx opts (n:ns) (Unshared $ LocalVar 0) <> ":" <>
             ppTermInCtx opts ns tp <> ",") : (helper opts (n:ns) ctx)

instance PrettyInCtx SawDoc where
  prettyInCtx pp = return pp

instance PrettyInCtx Type where
  prettyInCtx (Type t) = prettyInCtx t

instance PrettyInCtx MRVar where
  prettyInCtx (MRVar ec) = return $ ppName $ ecName ec

instance PrettyInCtx a => PrettyInCtx [a] where
  prettyInCtx xs = list <$> mapM prettyInCtx xs

instance {-# OVERLAPPING #-} PrettyInCtx String where
  prettyInCtx str = return $ fromString str

instance PrettyInCtx Text where
  prettyInCtx str = return $ fromString $ unpack str

instance PrettyInCtx Int where
  prettyInCtx i = return $ viaShow i

instance PrettyInCtx Natural where
  prettyInCtx i = return $ viaShow i

instance PrettyInCtx a => PrettyInCtx (Maybe a) where
  prettyInCtx (Just x) = (<+>) "Just" <$> prettyInCtx x
  prettyInCtx Nothing = return "Nothing"

instance (PrettyInCtx a, PrettyInCtx b) => PrettyInCtx (Either a b) where
  prettyInCtx (Left  a) = (<+>) "Left"  <$> prettyInCtx a
  prettyInCtx (Right b) = (<+>) "Right" <$> prettyInCtx b

instance (PrettyInCtx a, PrettyInCtx b) => PrettyInCtx (a,b) where
  prettyInCtx (x, y) = (\x' y' -> parens (x' <> "," <> y')) <$> prettyInCtx x
                                                            <*> prettyInCtx y

instance PrettyInCtx TermProj where
  prettyInCtx TermProjLeft = return (pretty '.' <> "1")
  prettyInCtx TermProjRight = return (pretty '.' <> "2")
  prettyInCtx (TermProjRecord fld) = return (pretty '.' <> pretty fld)

instance PrettyInCtx FunName where
  prettyInCtx (CallSName var) = prettyInCtx var
  prettyInCtx (EVarFunName var) = prettyInCtx var
  prettyInCtx (GlobalName g projs) =
    foldM (\pp proj -> (pp <>) <$> prettyInCtx proj) (ppName $
                                                      globalDefName g) projs

instance PrettyInCtx Comp where
  prettyInCtx (CompTerm t) = prettyInCtx t
  prettyInCtx (CompBind c f) =
    prettyAppList [prettyInCtx c, return ">>=", prettyInCtx f]
  prettyInCtx (CompReturn t) =
    prettyAppList [return "retS", return "_",
                   parens <$> prettyInCtx t]

instance PrettyInCtx CompFun where
  prettyInCtx (CompFunTerm _ t) = prettyInCtx t
  prettyInCtx (CompFunReturn _ t) =
    prettyAppList [return "retS", return "_",
                   parens <$> prettyInCtx t]
  prettyInCtx (CompFunComp f g) =
    prettyAppList [prettyInCtx f, return ">=>", prettyInCtx g]

instance PrettyInCtx NormComp where
  prettyInCtx (RetS t) =
    prettyAppList [return "retS", return "_", return "_",
                   parens <$> prettyInCtx t]
  prettyInCtx (ErrorS str) =
    prettyAppList [return "errorS", return "_", return "_",
                   parens <$> prettyInCtx str]
  prettyInCtx (Ite cond t1 t2) =
    prettyAppList [return "ite", return "_", parens <$> prettyInCtx cond,
                   parens <$> prettyInCtx t1, parens <$> prettyInCtx t2]
  prettyInCtx (Eithers elims eith) =
    prettyAppList [return "eithers", return (parens "SpecM _ _"),
                   prettyInCtx (map snd elims), parens <$> prettyInCtx eith]
  prettyInCtx (MaybeElim tp m f mayb) =
    prettyAppList [return "maybe", parens <$> prettyInCtx tp,
                   return (parens "SpecM _ _"), parens <$> prettyInCtx m,
                   parens <$> prettyInCtx f, parens <$> prettyInCtx mayb]
  prettyInCtx (OrS t1 t2) =
    prettyAppList [return "orS", return "_", return "_",
                   parens <$> prettyInCtx t1, parens <$> prettyInCtx t2]
  prettyInCtx (AssertBoolBind cond k) =
    prettyAppList [return "assertBoolS", return "_",
                   parens <$> prettyInCtx cond, return ">>=",
                   parens <$> prettyInCtx k]
  prettyInCtx (AssumeBoolBind cond k) =
    prettyAppList [return "assumeBoolS", return "_",
                   parens <$> prettyInCtx cond, return ">>=",
                   parens <$> prettyInCtx k]
  prettyInCtx (ExistsBind tp k) =
    prettyAppList [return "existsS", return "_", prettyInCtx tp,
                   return ">>=", parens <$> prettyInCtx k]
  prettyInCtx (ForallBind tp k) =
    prettyAppList [return "forallS", return "_", prettyInCtx tp,
                   return ">>=", parens <$> prettyInCtx k]
  prettyInCtx (FunBind f args (CompFunReturn _ _)) =
    snd $ prettyInCtxFunBindH f args
  prettyInCtx (FunBind f args k)
    | (g, m) <- prettyInCtxFunBindH f args =
    prettyAppList [g <$> m, return ">>=", prettyInCtx k]

-- | A helper function for the 'FunBind' case of 'prettyInCtx'. Returns the
-- string you would get if the associated 'CompFun' is 'CompFunReturn', as well
-- as a 'SawDoc' function (which is either 'id' or 'parens') to apply in the
-- case where the associated 'CompFun' is something else.
prettyInCtxFunBindH :: FunName -> [Term] ->
                       (SawDoc -> SawDoc, PPInCtxM SawDoc)
prettyInCtxFunBindH f [] = (id, prettyInCtx f)
prettyInCtxFunBindH f args = (parens,) $
  prettyTermApp (funNameTerm f) args
