{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

{- |
Module      : SAWCentral.MRSolver.SMT
Copyright   : Galois, Inc. 2022
License     : BSD3
Maintainer  : westbrook@galois.com
Stability   : experimental
Portability : non-portable (language extensions)

This module implements the interface between Mr. Solver and an SMT solver,
namely 'mrProvable' and 'mrProveEq'.
-}

module SAWCentral.MRSolver.SMT where

import Data.Maybe
import qualified Data.Text as Text
import Data.Text (Text)
import qualified Data.Vector as V
import Numeric.Natural (Natural)
import Control.Monad (MonadPlus(..), (>=>), (<=<), when, unless, foldM)
import Control.Monad.Catch (throwM, catch)
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Trans.Class (MonadTrans(..))
import Control.Monad.Trans.Maybe
import GHC.Generics

import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set

import Prettyprinter
import Data.Reflection
import Data.Parameterized.BoolRepr

import qualified SAWSupport.Pretty as PPS (render)

import SAWCore.Term.Functor
import SAWCore.Term.Pretty
import SAWCore.SharedTerm
import SAWCore.Recognizer

import SAWCore.Module (Def(..))
import SAWCore.Prim (widthNat, EvalError(..))
import qualified SAWCore.Prim as Prim
import SAWCore.Simulator (SimulatorConfig, evalSharedTerm)
import SAWCore.Simulator.Value
import SAWCore.Simulator.TermModel
import SAWCore.Simulator.Prims
import SAWCore.FiniteValue

import SAWCentral.Panic
import SAWCentral.Proof (termToProp, propToTerm, prettyProp, propToSequent, SolveResult(..))

import SAWCentral.MRSolver.Term
import SAWCentral.MRSolver.Monad


----------------------------------------------------------------------
-- * Normalizing terms for SMT
----------------------------------------------------------------------

type TmPrim = Prim TermModel

-- | Convert a vec value to a 'Term'
vecValToTerm :: SharedContext -> SimulatorConfig TermModel ->
                TValue TermModel -> Value TermModel -> IO (Maybe Term)
vecValToTerm sc cfg tp (VVector vs) =
  do let ?recordEC = \_ec -> return ()
     tp' <- readBackTValue sc cfg tp
     vs' <- traverse (readBackValue sc cfg tp <=< force) (V.toList vs)
     Just <$> scVectorReduced sc tp' vs'
vecValToTerm _ _ _ (VExtra (VExtraTerm _tp tm)) = return $ Just tm
vecValToTerm _ _ _ _ = return $ Nothing

-- | A primitive function that expects a term of the form @gen n a f@ and the
-- function argument @f@ to the supplied function
primGenVec :: SharedContext -> SimulatorConfig TermModel ->
              TValue TermModel -> (Term -> TmPrim) -> TmPrim
primGenVec sc cfg tp =
  PrimFilterFun "primGenVec" $ \v -> lift (vecValToTerm sc cfg tp v) >>= \case
    (Just (asGenVecTerm -> Just (_, _, f_m))) -> lift $ f_m sc
    _ -> mzero

-- | Convert a Boolean value to a 'Term'
boolValToTerm :: SharedContext -> Value TermModel -> IO Term
boolValToTerm _ (VBool (Left tm)) = return tm
boolValToTerm sc (VBool (Right b)) = scBool sc b
boolValToTerm _ (VExtra (VExtraTerm _tp tm)) = return tm
boolValToTerm _ v = error ("boolValToTerm: unexpected value: " ++ show v)

-- | Convert a bitvector value to a 'Term'
bvValToTerm :: SharedContext -> Value TermModel -> IO Term
bvValToTerm _ (VWord (Left (_,tm))) = return tm
bvValToTerm sc (VWord (Right bv)) =
  scBvConst sc (fromIntegral (Prim.width bv)) (Prim.unsigned bv)
bvValToTerm sc (VVector vs) =
  do vs' <- traverse (boolValToTerm sc <=< force) (V.toList vs)
     bool_tp <- scBoolType sc
     scVectorReduced sc bool_tp vs'
bvValToTerm _ (VExtra (VExtraTerm _tp tm)) = return tm
bvValToTerm _ v = error ("bvValToTerm: unexpected value: " ++ show v)

-- | Convert a natural number value to a 'Term'
natValToTerm :: SharedContext -> Value TermModel -> IO Term
natValToTerm sc (VNat n) = scNat sc n
natValToTerm sc (VBVToNat w bv_val) =
  do bv_tm <- bvValToTerm sc bv_val
     scBvToNat sc (fromIntegral w) bv_tm
natValToTerm _ (VExtra (VExtraTerm _ n)) = return n
natValToTerm _ v = error ("natValToTerm: unexpected value: " ++ show v)

-- | A primitive function that expects a 'Term' of type @Nat@
primNatTermFun :: SharedContext -> (Term -> TmPrim) -> TmPrim
primNatTermFun sc =
  PrimFilterFun "primNatTermFun" $ \v -> lift (natValToTerm sc v)

-- | A primitive that returns a global as a term
primGlobal :: SharedContext -> Ident -> TmPrim
primGlobal sc glob =
  Prim $ do tp <- scTypeOfIdent sc glob
            tp_tp <- scTypeOf sc tp >>= scWhnf sc
            s <- case asSort tp_tp of
              Just s -> return s
              Nothing -> fail "primGlobal: expected sort"
            VExtra <$> VExtraTerm (VTyTerm s tp) <$> scGlobalDef sc glob

-- | A primitive that unfolds a global
primUnfold :: SharedContext -> SimulatorConfig TermModel -> Ident -> TmPrim
primUnfold sc cfg glob =
  Prim $ evalSharedTerm cfg =<< fmap (fromJust . defBody) (scRequireDef sc glob)

mkReflProof :: SharedContext -> Bool -> IO TmValue
mkReflProof sc b =
  do b_trm <- scBool sc b
     bool_tp <- scBoolType sc
     refl_trm <- scCtorApp sc "Prelude.Refl" [bool_tp, b_trm]
     eq_tp <- scDataTypeApp sc "Prelude.Eq" [bool_tp, b_trm, b_trm]
     return $ VExtra $ VExtraTerm (VTyTerm propSort eq_tp) refl_trm

mkDummyProofValue :: Text -> IO (Thunk TermModel)
mkDummyProofValue op =
  delay $ return $ panic op ["Unexpected evaluation of proof object"]

iteWithProofOp :: SharedContext -> SimulatorConfig TermModel -> TmPrim
iteWithProofOp sc cfg =
  tvalFun $ \tp ->
  boolFun $ \b_val ->
  strictFun $ \x_fun ->
  strictFun $ \y_fun ->
  Prim $
  case b_val of
    Right b -> mkReflProof sc b >>= apply x_fun . ready
    Left b_trm ->
      do let ?recordEC = \_ec -> return ()
         eq_true <- mkDummyProofValue "iteWithProofOp / true"
         x <- apply x_fun eq_true
         x_trm <- readBackValue sc cfg tp x
         eq_false <- mkDummyProofValue "iteWithProofOp / false"
         y <- apply y_fun eq_false
         y_trm <- readBackValue sc cfg tp y
         tp_trm <- readBackTValue sc cfg tp
         ite_trm <- scIte sc tp_trm b_trm x_trm y_trm
         return $ VExtra $ VExtraTerm tp ite_trm

-- | Implementations of primitives for normalizing Mr Solver terms
-- FIXME: eventually we need to add the current event type to this list
smtNormPrims :: SharedContext -> SimulatorConfig TermModel ->
                Map Ident TmPrim -> Map Ident TmPrim
smtNormPrims sc cfg = Map.union $ Map.fromList
  [
    -- Override the usual behavior of @gen@, @genWithProof@, and @VoidEv@ so
    -- they are not evaluated or unfolded
    ("Prelude.gen", primGlobal sc "Prelude.gen"),
    ("Prelude.genWithProof", primGlobal sc "Prelude.genWithProof"),
    ("SpecM.VoidEv", primGlobal sc "SpecM.VoidEv"),
    ("SpecM.SpecM", primGlobal sc "SpecM.SpecM"),

    -- Normalize an application of @atwithDefault@ to a @gen@ term into an
    -- application of the body of the gen term to the index. Note that this
    -- implicitly assumes that the index is always in bounds, MR solver always
    -- checks that before it creates an indexing term.
    ("Prelude.atWithDefault",
     PrimFun $ \_len -> tvalFun $ \a -> PrimFun $ \_errVal ->
      primGenVec sc cfg a $ \f -> primNatTermFun sc $ \ix ->
      Prim (do tm <- scApplyBeta sc f ix
               tm' <- smtNorm sc tm
               return $ VExtra $ VExtraTerm a tm')
    ),

    -- Normalize an application of @atWithProof@ to a @gen@ term by applying the
    -- function of the @gen@ to the index
    ("Prelude.atWithProof",
     PrimFun $ \_len -> tvalFun $ \a -> primGenVec sc cfg a $ \f ->
      primNatTermFun sc $ \ix -> PrimFun $ \_pf ->
      Prim (do tm <- scApplyBeta sc f ix
               tm' <- smtNorm sc tm
               return $ VExtra $ VExtraTerm a tm')
    ),

    -- Override iteWithProof so it unfolds to a normal ite with dummy proof objects
    ("Prelude.iteWithProof", iteWithProofOp sc cfg)
  ]

-- | A version of 'mrNormTerm' in the 'IO' monad, and which does not add any
-- debug output. This is used to re-enter the normalizer from inside the
-- primitives.
smtNorm :: SharedContext -> Term -> IO Term
smtNorm sc t =
  scGetModuleMap sc >>= \modmap ->
  normalizeSharedTerm' sc modmap (smtNormPrims sc) Map.empty Set.empty t

-- | Normalize a 'Term' using some Mr Solver specific primitives
mrNormTerm :: Term -> MRM t Term
mrNormTerm t =
  mrDebugPrint 2 "Normalizing term:" >>
  mrDebugPPInCtx 2 t >>
  liftSC1 smtNorm t

-- | Normalize an open term by wrapping it in lambdas, normalizing, and then
-- removing those lambdas
mrNormOpenTerm :: Term -> MRM t Term
mrNormOpenTerm body =
  do length_ctx <- mrVarCtxLength <$> mrUVars
     fun_term <- lambdaUVarsM body
     normed_fun <- mrNormTerm fun_term
     return (peel_lambdas length_ctx normed_fun)
       where
         peel_lambdas :: Int -> Term -> Term
         peel_lambdas 0 t = t
         peel_lambdas i (asLambda -> Just (_, _, t)) = peel_lambdas (i-1) t
         peel_lambdas _ _ = error "mrNormOpenTerm: unexpected non-lambda term!"


----------------------------------------------------------------------
-- * Checking Provability with SMT
----------------------------------------------------------------------

-- | Test if a closed Boolean term is \"provable\", i.e., its negation is
-- unsatisfiable, using an SMT solver. By \"closed\" we mean that it contains no
-- uvars or 'MRVar's.
--
-- FIXME: use the timeout!
mrProvableRaw :: Term -> MRM t Bool
mrProvableRaw prop_term =
  do sc <- mrSC
     prop <- liftSC1 termToProp prop_term
     unints <- Set.map ecVarIndex <$> getAllExtSet <$> liftSC1 propToTerm prop
     nenv <- liftIO (scGetNamingEnv sc)
     opts <- mrPPOpts
     mrDebugPrint 2 ("Calling SMT solver with proposition: " ++
                     prettyProp opts nenv prop)
     -- If there are any saw-core `error`s in the term, this will throw a
     -- Haskell error - in this case we want to just return False, not stop
     -- execution
     smt_res <-
       (Right <$> mrAskSMT unints (propToSequent prop))
         `catch` \case
           UserError msg -> return $ Left msg
           e -> throwM e
     case smt_res of
       Left msg ->
         mrDebugPrint 2 ("SMT solver encountered a saw-core error term: " ++ msg)
           >> return False
       Right (stats, SolveUnknown) ->
          mrDebugPrint 2 "SMT solver response: unknown" >>
          recordUsedSolver stats prop_term >> return False
       Right (stats, SolveCounterexample cex) ->
         mrDebugPrint 2 "SMT solver response: not provable" >>
         mrDebugPrint 3 ("Counterexample:" ++ concatMap (\(x,v) ->
           "\n - " ++ show (ppName $ ecName x) ++
           " = " ++ PPS.render opts (ppFirstOrderValue opts v)) cex) >>
         recordUsedSolver stats prop_term >> return False
       Right (stats, SolveSuccess _) ->
         mrDebugPrint 2 "SMT solver response: provable" >>
         recordUsedSolver stats prop_term >> return True

-- | Test if a Boolean term over the current uvars is provable given the current
-- assumptions
mrProvable :: Term -> MRM t Bool
mrProvable (asBool -> Just b) = return b
mrProvable bool_tm =
  do mrUVars >>= mrDebugPPPrefix 3 "mrProvable uvars:"
     assumps <- mrAssumptions
     prop <- liftSC2 scImplies assumps bool_tm >>= liftSC1 scEqTrue
     prop_inst <- instantiateUVarsM instUVar prop >>= mrSubstLowerEVars
     mrNormTerm prop_inst >>= mrProvableRaw
  where -- | Create a new global variable of the given name and type
        instUVar :: LocalName -> Term -> MRM t Term
        instUVar nm =
          liftSC1 scWhnf >=> liftSC2 scFreshEC nm >=> liftSC1 scExtCns


----------------------------------------------------------------------
-- * Unifying BVVec and Vec Lengths
----------------------------------------------------------------------

-- | The length of a vector, given as either ...
data VecLength = ConstBVVecLen Natural Natural
               | ConstNatVecLen Natural Natural
               | SymBVVecLen Natural Term
               | SymNatVecLen Term
               deriving (Generic, Show, TermLike)

instance PrettyInCtx VecLength where
  prettyInCtx (ConstBVVecLen n len) =
    prettyAppList [return "ConstBVVecLen", prettyInCtx n, prettyInCtx len]
  prettyInCtx (ConstNatVecLen n len) =
    prettyAppList [return "ConstNatVecLen", prettyInCtx n, prettyInCtx len]
  prettyInCtx (SymBVVecLen n len) =
    prettyAppList [return "SymBVVecLen", prettyInCtx n, parens <$> prettyInCtx len]
  prettyInCtx (SymNatVecLen len) =
    prettyAppList [return "SymNatVecLen", parens <$> prettyInCtx len]

-- | Convert a natural number expression to a 'VecLength'
asVecLen :: Term -> VecLength
asVecLen (asBvToNatKnownW -> Just (n, len))
  | Just len' <- asUnsignedConcreteBv len = ConstBVVecLen n len'
  | otherwise = SymBVVecLen n len
asVecLen (asUnsignedConcreteBvToNat -> Just len) =
  ConstNatVecLen (widthNat len) len
asVecLen len = SymNatVecLen len

-- | Recognize a @BVVec@, @Vec@, or @mseq (TCNum ...)@ vector with length
-- represented as a 'VecLength'
asVecTypeWithLen :: Recognizer Term (VecLength, Term)
asVecTypeWithLen (asApplyAll -> (isGlobalDef "Prelude.BVVec" -> Just (),
                                 [asNat -> Just n, len, a]))
  | Just len' <- asUnsignedConcreteBv len = Just (ConstBVVecLen n len', a)
  | otherwise = Just (SymBVVecLen n len, a)
asVecTypeWithLen (asVectorType -> Just (len, a)) = Just (asVecLen len, a)
asVecTypeWithLen (asApplyAll -> (isGlobalDef "SpecM.mseq" -> Just (),
                                 [_, asNum -> Just (Left len), a])) =
  Just (asVecLen len, a)
asVecTypeWithLen _ = Nothing

-- | Convert a 'VecLength' into either a 'Term' of bitvector type with the given
-- 'Natural' bit-width if the 'VecLength' has an associated bit-width, or into a
-- 'Term' of nat type otherwise
mrVecLenAsBVOrNatTerm :: VecLength -> MRM t (Either (Natural, Term) Term)
mrVecLenAsBVOrNatTerm (ConstBVVecLen n len) =
  (Left . (n,)) <$> liftSC2 scBvLit n (fromIntegral len)
mrVecLenAsBVOrNatTerm (ConstNatVecLen n len) =
  (Left . (n,)) <$> liftSC2 scBvLit n (fromIntegral len)
mrVecLenAsBVOrNatTerm (SymBVVecLen n len) =
  return $ Left (n, len)
mrVecLenAsBVOrNatTerm (SymNatVecLen len) =
  return $ Right len

-- | Get the type of an index bounded by a 'VecLength'
mrVecLenIxType :: VecLength -> MRM t Term
mrVecLenIxType vlen = mrVecLenAsBVOrNatTerm vlen >>= \case
  Left (n, _) -> liftSC1 scBitvector n
  Right _ -> liftSC0 scNatType

-- | Construct the proposition that the given 'Term' of type 'mrVecLenIxType'
-- is less than the given 'VecLength'
mrVecLenIxBound :: VecLength -> Term -> MRM t Term
mrVecLenIxBound vlen ix = mrVecLenAsBVOrNatTerm vlen >>= \case
  Left (n, len) -> liftSC1 scNat n >>= \n' ->
                   liftSC2 scGlobalApply "Prelude.bvult" [n', ix, len]
  Right len -> liftSC2 scGlobalApply "Prelude.ltNat" [ix, len]

-- | Test if two vector lengths are equal, and if so, generalize them to use the
-- same index type as returned by 'mrVecLenIxType'
mrVecLenUnify :: VecLength -> VecLength -> MRM t (Maybe (VecLength, VecLength))
mrVecLenUnify (ConstBVVecLen n1 len1) (ConstBVVecLen n2 len2)
  | n1 == n2 && len1 == len2
  = return $ Just (ConstBVVecLen n1 len1, ConstBVVecLen n2 len2)
mrVecLenUnify (ConstBVVecLen n1 len1) (ConstNatVecLen n2 len2)
  | n2 < n1 && len1 == len2
  = return $ Just (ConstBVVecLen n1 len1, ConstNatVecLen n1 len2)
mrVecLenUnify (ConstNatVecLen n1 len1) (ConstBVVecLen n2 len2)
  | n1 < n2 && len1 == len2
  = return $ Just (ConstNatVecLen n2 len1, ConstBVVecLen n2 len2)
mrVecLenUnify (ConstNatVecLen n1 len1) (ConstNatVecLen n2 len2)
  | len1 == len2, nMax <- max n1 n2
  = return $ Just (ConstNatVecLen nMax len1, ConstNatVecLen nMax len2)
mrVecLenUnify vlen1@(SymBVVecLen n1 len1) vlen2@(SymBVVecLen n2 len2)
  | n1 == n2
  = mrProveEq len1 len2 >>= \case
      True -> return $ Just (vlen1, vlen2)
      False -> return Nothing
mrVecLenUnify (SymNatVecLen len1) (SymNatVecLen len2) =
  mrProveEq len1 len2 >>= \case
    True -> return $ Just (SymNatVecLen len1, SymNatVecLen len2)
    False -> return Nothing
mrVecLenUnify _ _ = return Nothing

-- | Given a vector length, element type, and generating function, return the
-- associated vector formed using the appropritate @gen@ function
mrVecLenGen :: VecLength -> Term -> Term -> MRM t Term
mrVecLenGen (ConstBVVecLen n len) tp f =
  do n_tm <- liftSC1 scNat n
     len_tm <- liftSC2 scBvLit n (fromIntegral len)
     mrApplyGlobal "Prelude.genBVVecNoPf" [n_tm, len_tm, tp, f]
mrVecLenGen (ConstNatVecLen n len) tp f =
  do n_tm <- liftSC1 scNat n
     len_tm <- liftSC1 scNat len
     nat_tp <- liftSC0 scNatType
     f' <- mrLambdaLift1 ("ix", nat_tp) f $ \x f' ->
        liftSC2 scBvNat n_tm x >>= mrApply f'
     mrApplyGlobal "Prelude.gen" [len_tm, tp, f']
mrVecLenGen (SymBVVecLen n len) tp f =
  do n_tm <- liftSC1 scNat n
     mrApplyGlobal "Prelude.genBVVecNoPf" [n_tm, len, tp, f]
mrVecLenGen (SymNatVecLen len) tp f =
  do mrApplyGlobal "Prelude.gen" [len, tp, f]

-- | Given a vector length, element type, vector of that length and type, and an
-- index of type 'mrVecLenIxType', index into the vector
mrVecLenAt :: VecLength -> Term -> Term -> Term -> MRM t Term
mrVecLenAt (ConstBVVecLen n len) tp v ix =
  do n_tm <- liftSC1 scNat n
     len_tm <- liftSC2 scBvLit n (fromIntegral len)
     mrAtBVVec n_tm len_tm tp v ix
mrVecLenAt (ConstNatVecLen n len) tp v ix =
  do len_tm <- liftSC1 scNat len
     ix' <- liftSC2 scBvToNat n ix
     mrAtVec len_tm tp v ix'
mrVecLenAt (SymBVVecLen n len) tp v ix =
  do n_tm <- liftSC1 scNat n
     mrAtBVVec n_tm len tp v ix
mrVecLenAt (SymNatVecLen len) tp v ix =
  do mrAtVec len tp v ix


----------------------------------------------------------------------
-- * SMT-Friendly Representations
----------------------------------------------------------------------

-- | A representation of some subset of the elements of a type @tp@ as elements
-- of some other type @tp_r@. The idea is that the type @tp_r@ is easier to
-- represent in SMT solvers.
--
-- This is captured formally with a function @r@ from elements of the
-- representation type @tp_r@ to the elements of type @tp@ that they represent
-- along with an equivalence relation @eq_r@ on @tp_r@ such that @r@ is
-- injective when viewed as a morphism from @eq_r@ to the natural equivalence
-- relation @equiv@ of @tp@. In more detail, this means that @eq_r@ holds
-- between two inputs to @r@ iff @equiv@ holds between their outputs. Note that
-- an injective representation need not be surjective, meaning there could be
-- elements of @tp@ that it cannot represent.
data InjectiveRepr
     -- | The identity representation of @(tp,equiv)@ by itself. Only applies to
     -- non-vector types, as vectors should be represented by one of the vector
     -- representations.
  = InjReprId
    -- | A representation of a numeric type (@Num@, @Nat@, or @Vec n Bool@) by
    -- another numeric type defined as the composition of one or more injective
    -- numeric representations. NOTE: we do not expect numeric representations
    -- to occur inside other representations like those for pairs and vectors
  | InjReprNum [InjNumRepr]
    -- | A representation of the pair type @tp1 * tp2@ by @tp_r1 * tp_r2@ using
    -- representations of @tp1@ and @tp2@
  | InjReprPair InjectiveRepr InjectiveRepr
    -- | A representation of the vector type @Vec len tp@ by the functional type
    -- @tp_len -> tp_r@ from indices to elements of the representation type
    -- @tp_r@ of @tp@, given a representation of @tp@ by @tp_r@, where the index
    -- type @tp_len@ is determined by the 'VecLength'
  | InjReprVec VecLength Term InjectiveRepr
  deriving (Generic, Show, TermLike)

-- | A representation of a numeric type (@Num@, @Nat@, or @Vec n Bool@) by
-- another numeric type defined as an injective function
data InjNumRepr
     -- | The @TCNum@ constructor as a representation of @Num@ by @Nat@
  = InjNatToNum
    -- | The @bvToNat@ function as a representation of @Nat@ by @Vec n Bool@
  | InjBVToNat Natural
  deriving (Generic, Show, TermLike)

instance PrettyInCtx InjectiveRepr where
  prettyInCtx InjReprId = return "InjReprId"
  prettyInCtx (InjReprNum steps) =
    prettyAppList [return "InjReprNum", list <$> mapM prettyInCtx steps]
  prettyInCtx (InjReprPair r1 r2) =
    prettyAppList [return "InjReprPair", parens <$> prettyInCtx r1,
                                         parens <$> prettyInCtx r2]
  prettyInCtx (InjReprVec n tp repr) =
    prettyAppList [return "InjReprVec", parens <$> prettyInCtx n,
                                        parens <$> prettyInCtx tp,
                                        parens <$> prettyInCtx repr]

instance PrettyInCtx InjNumRepr where
  prettyInCtx InjNatToNum = return "InjNatToNum"
  prettyInCtx (InjBVToNat n) =
    prettyAppList [return "InjBVToNat", prettyInCtx n]

-- | Smart constructor for pair representations, that combines a pair of
-- identity representations into an identity representation on the pair type
injReprPair :: InjectiveRepr -> InjectiveRepr -> InjectiveRepr
injReprPair InjReprId InjReprId = InjReprId
injReprPair repr1 repr2 = InjReprPair repr1 repr2

-- | Test if there is a non-identity numeric representation from the first to
-- the second type
findNumRepr :: Term -> Term -> Maybe InjectiveRepr
findNumRepr (asBitvectorType -> Just n) (asNumType -> Just ()) =
  Just $ InjReprNum [InjBVToNat n, InjNatToNum]
findNumRepr (asBitvectorType -> Just n) (asNatType -> Just ()) =
  Just $ InjReprNum [InjBVToNat n]
findNumRepr (asNatType -> Just ()) (asNumType -> Just ()) =
  Just $ InjReprNum [InjNatToNum]
findNumRepr _ _ = Nothing

-- | Compose two injective representations, assuming that they do compose, i.e.,
-- that the output type of the first equals the input type of the second
injReprComp :: InjectiveRepr -> InjectiveRepr -> InjectiveRepr
injReprComp InjReprId r = r
injReprComp r InjReprId = r
injReprComp (InjReprNum steps1) (InjReprNum steps2) =
  InjReprNum (steps1 ++ steps2)
injReprComp (InjReprPair r1_l r1_r) (InjReprPair r2_l r2_r) =
  InjReprPair (injReprComp r1_l r2_l) (injReprComp r1_r r2_r)
injReprComp r1 r2 =
  panic "injReprComp" [
      "Representations do not compose: " <>
          Text.pack (show r1) <> " and " <> Text.pack (show r2)
  ]

-- | Apply a 'InjectiveRepr' to convert an element of the representation type
-- @tp_r@ to the type @tp@ that it represents
mrApplyRepr :: InjectiveRepr -> Term -> MRM t Term
mrApplyRepr InjReprId t = return t
mrApplyRepr (InjReprNum steps) t_top = foldM applyStep t_top steps where
  applyStep t InjNatToNum = liftSC2 scCtorApp "Cryptol.TCNum" [t]
  applyStep t (InjBVToNat n) = liftSC2 scBvToNat n t
mrApplyRepr (InjReprPair repr1 repr2) t =
  do t1 <- mrApplyRepr repr1 =<< doTermProj t TermProjLeft
     t2 <- mrApplyRepr repr2 =<< doTermProj t TermProjRight
     liftSC2 scPairValueReduced t1 t2
mrApplyRepr (InjReprVec vlen tp repr) t =
  do ix_tp <- mrVecLenIxType vlen
     f <- mrLambdaLift1 ("ix", ix_tp) (repr, t) $ \x (repr', t') ->
       mrApplyRepr repr' =<< mrApply t' x
     mrVecLenGen vlen tp f

newtype MaybeTerm b = MaybeTerm { unMaybeTerm :: If b Term () }

-- | Apply a monadic 'Term' operation to a 'MaybeTerm'
mapMaybeTermM :: Monad m => BoolRepr b -> (Term -> m Term) -> MaybeTerm b ->
                 m (MaybeTerm b)
mapMaybeTermM TrueRepr f (MaybeTerm t) = MaybeTerm <$> f t
mapMaybeTermM FalseRepr _ _ = return $ MaybeTerm ()

-- | Apply a binary monadic 'Term' operation to a 'MaybeTerm'
map2MaybeTermM :: Monad m => BoolRepr b -> (Term -> Term -> m Term) ->
                  MaybeTerm b -> MaybeTerm b -> m (MaybeTerm b)
map2MaybeTermM TrueRepr f (MaybeTerm t1) (MaybeTerm t2) = MaybeTerm <$> f t1 t2
map2MaybeTermM FalseRepr _ _ _ = return $ MaybeTerm ()

instance Given (BoolRepr b) => TermLike (MaybeTerm b) where
  mapTermLike = mapMaybeTermM given

-- | Construct an injective representation for a type @tp@ and an optional term
-- @tm@ of that type, returning the representation type @tp_r@, the optional
-- term @tm_r@ that represents @tm@, and the representation itself. If there is
-- a choice, choose the representation that works best for SMT solvers.
mkInjRepr :: BoolRepr b -> Term -> MaybeTerm b ->
             MRM t (Term, MaybeTerm b, InjectiveRepr)
mkInjRepr TrueRepr _ (MaybeTerm (asNum -> Just (Left t))) =
  do nat_tp <- liftSC0 scNatType
     (tp_r, tm_r, r) <- mkInjRepr TrueRepr nat_tp (MaybeTerm t)
     return (tp_r, tm_r, injReprComp r (InjReprNum [InjNatToNum]))
mkInjRepr TrueRepr _ (MaybeTerm (asBvToNatKnownW -> Just (n, t))) =
  do bv_tp <- liftSC1 scBitvector n
     return (bv_tp, MaybeTerm t, InjReprNum [InjBVToNat n])
mkInjRepr b (asPairType -> Just (tp1, tp2)) t =
  do tm1 <- mapMaybeTermM b (flip doTermProj TermProjLeft) t
     tm2 <- mapMaybeTermM b (flip doTermProj TermProjRight) t
     (tp_r1, tm_r1, r1) <- mkInjRepr b tp1 tm1
     (tp_r2, tm_r2, r2) <- mkInjRepr b tp2 tm2
     tp_r <- liftSC2 scPairType tp_r1 tp_r2
     tm_r <- map2MaybeTermM b (liftSC2 scPairValueReduced) tm_r1 tm_r2
     return (tp_r, tm_r, InjReprPair r1 r2)

mkInjRepr b (asVecTypeWithLen -> Just (vlen, tp@(asBoolType -> Nothing))) tm =
  do ix_tp <- mrVecLenIxType vlen
     -- NOTE: these return values from mkInjRepr all have ix free
     (tp_r', tm_r', r') <-
       give b $
       withUVarLift "ix" (Type ix_tp) (vlen,tp,tm) $ \ix (vlen',tp',tm') ->
       do tm_elem <-
            mapMaybeTermM b (\tm'' -> mrVecLenAt vlen' tp' tm'' ix) tm'
          mkInjRepr b tp' tm_elem
     -- r' should not have ix free, so it should be ok to substitute an error
     -- term for ix...
     r <- substTermLike 0 [error
                           "mkInjRepr: unexpected free ix variable in repr"] r'
     tp_r <- liftSC3 scPi "ix" ix_tp tp_r'
     tm_r <- mapMaybeTermM b (liftSC3 scLambda "ix" ix_tp) tm_r'
     return (tp_r, tm_r, InjReprVec vlen tp r)

mkInjRepr _ tp tm = return (tp, tm, InjReprId)


-- | Specialization of 'mkInjRepr' with no element of the represented type
mkInjReprType :: Term -> MRM t (Term, InjectiveRepr)
mkInjReprType tp =
  (\(tp_r,_,repr) -> (tp_r,repr)) <$> mkInjRepr FalseRepr tp (MaybeTerm ())

-- | Specialization of 'mkInjRepr' with an element of the represented type
mkInjReprTerm :: Term -> Term -> MRM t (Term, Term, InjectiveRepr)
mkInjReprTerm tp trm =
  (\(tp_r, tm, repr) -> (tp_r, unMaybeTerm tm, repr)) <$>
  mkInjRepr TrueRepr tp (MaybeTerm trm)


-- | Given two representations @r1@ and @r2@ along with their representation
-- types @tp_r1@ and @tp_r2, try to unify their representation types, yielding
-- new versions of those representations. That is, try to find a common type
-- @tp_r@ and representations @r1'@ and @r2'@ such that the following picture
-- holds:
--
-- >   tp1      tp2
-- >    ^        ^
-- > r1 |        | r2
-- >  tp_r1    tp_r2
-- >    ^        ^
-- > r1' \      / r2'
-- >      \    /
-- >       tp_r
--
injUnifyReprTypes :: Term -> InjectiveRepr -> Term -> InjectiveRepr ->
                     MaybeT (MRM t) (Term, InjectiveRepr, InjectiveRepr)

-- If there is a numeric coercion from one side to the other, use it to unify
-- the two input representations
injUnifyReprTypes tp1 r1 tp2 r2
  | Just r2' <- findNumRepr tp1 tp2
  = return (tp1, r1, injReprComp r2' r2)
injUnifyReprTypes tp1 r1 tp2 r2
  | Just r1' <- findNumRepr tp2 tp1
  = return (tp2, injReprComp r1' r1, r2)

-- If both representations are the identity, make sure the repr types are equal
injUnifyReprTypes tp1 InjReprId tp2 InjReprId =
  do tps_eq <- lift $ mrConvertible tp1 tp2
     if tps_eq then return (tp1, InjReprId, InjReprId)
       else mzero

-- For pair representations, unify the two sides, treating an identity
-- representation as a pair of identity representations
injUnifyReprTypes tp1 (InjReprPair r1l r1r) tp2 (InjReprPair r2l r2r)
  | Just (tp1l, tp1r) <- asPairType tp1
  , Just (tp2l, tp2r) <- asPairType tp2 =
    do (tp_r_l, r1l', r2l') <- injUnifyReprTypes tp1l r1l tp2l r2l
       (tp_r_r, r1r', r2r') <- injUnifyReprTypes tp1r r1r tp2r r2r
       tp_r <- lift $ liftSC2 scPairType tp_r_l tp_r_r
       return (tp_r, InjReprPair r1l' r1r', InjReprPair r2l' r2r')
injUnifyReprTypes tp1 InjReprId tp2 r2
  | isJust (asPairType tp1)
  = injUnifyReprTypes tp1 (InjReprPair InjReprId InjReprId) tp2 r2
injUnifyReprTypes tp1 r1 tp2 InjReprId
  | isJust (asPairType tp2)
  = injUnifyReprTypes tp1 r1 tp2 (InjReprPair InjReprId InjReprId)

-- For vector types, check that the lengths are equal and unify the element
-- representations. Note that if either side uses a natural number length
-- instead of a bitvector length, both sides will need to, since we don't
-- currently have representation that can cast from a bitvector length to an
-- equal natural number length
injUnifyReprTypes _ (InjReprVec len1 tp1 r1) _ (InjReprVec len2 tp2 r2) =
  do (len1', len2') <- MaybeT $ mrVecLenUnify len1 len2
     ix_tp <- lift $ mrVecLenIxType len1'
     (tp_r, r1', r2') <- injUnifyReprTypes tp1 r1 tp2 r2
     tp_r_fun <- lift $ mrArrowType "ix" ix_tp tp_r
     return (tp_r_fun, InjReprVec len1' tp1 r1', InjReprVec len2' tp2 r2')

injUnifyReprTypes _ _ _ _ = mzero


-- | Given two types @tp1@ and @tp2@, try to find a common type @tp@ that
-- injectively represents both of them. Pictorially, the result looks like this:
--
-- >  tp1      tp2
-- >   ^        ^
-- > r1 \      / r2
-- >     \    /
-- >       tp
--
-- where @r1@ and @r2@ are injective representations. The representations should
-- be maximal, meaning that they represent as much of @tp1@ and @tp2@ as
-- possible. If there is such a @tp@, return it along with the representations
-- @r1@ and @r2@. Otherwise, return 'Nothing', meaning the unification failed.
injUnifyTypes :: Term -> Term ->
                 MRM t (Maybe (Term, InjectiveRepr, InjectiveRepr))
injUnifyTypes tp1 tp2 =
  do (tp_r1, r1) <- mkInjReprType tp1
     (tp_r2, r2) <- mkInjReprType tp2
     runMaybeT $ injUnifyReprTypes tp_r1 r1 tp_r2 r2


-- | Use one injective representations @r1@ to restrict the domain of another
-- injective representation @r2@, yielding an injective representation with the
-- same representation type as @r1@ and the same type being represented as @r2@.
-- Pictorially this looks like this:
--
-- >  tp1           tp2
-- >   ^            ^
-- >    \          / r2
-- > r1  \        /
-- >      \    tpr2
-- >       \    ^
-- >        \  / r2''
-- >        tpr1
--
-- The return value is the composition of @r2''@ and @r2@. It is an error if
-- this diagram does not exist.
injReprRestrict :: Term -> InjectiveRepr -> Term -> InjectiveRepr ->
                   MRM t InjectiveRepr

-- If tp1 and tp2 are numeric types with a representation from tp1 to tp2, we
-- can pre-compose that representation with r2
injReprRestrict tp1 _ tp2 r2
  | Just r2'' <- findNumRepr tp1 tp2
  = return $ injReprComp r2'' r2

-- In all other cases, the only repr that pre-composes with r2 is the identity
-- repr, so we just return r2
injReprRestrict _ _ _ r2 = return r2


-- | Take in a type @tp_r1@, a term @tm1@ of type @tp_r1@, an injective
-- representation @r1@ with @tp_r1@ as its representation type, and a type @tp2@
-- with an element @tm2@, and try to find a type @tp_r'@ and a term @tm'@ of
-- type @tp_r'@ that represents both @r1 tm1@ and @tm2@ using representations
-- @r1'@ and @r2'@, repsectively. That is, @r1'@ should represent @tp1@ and
-- @r2'@ should represent @tp2@, both with the same representation type @tp_r'@,
-- and should satisfy
--
-- > r1' tm' = r1 tm1    and    r2' tm' = tm2
--
-- In pictures the result should look like this:
--
-- >    r1 tm1      tm2::tp2
-- >      ^            ^
-- >   r1 |           /
-- >      |          /
-- >  tm1::tp_r1    / r2'
-- >       ^       /
-- >   r1'' \     /
-- >         \   /
-- >       tm'::tp_r'
--
-- where @r1'@ is the composition of @r1''@ and @r1@.
injUnifyRepr :: Term -> Term -> InjectiveRepr -> Term -> Term ->
                MRM t (Maybe (Term, Term, InjectiveRepr, InjectiveRepr))

-- If there is a numeric repr r2 from tp_r1 to tp2, then that's our r2',
-- assuming that r2 tm1 = tm2
injUnifyRepr tp_r1 tm1 r1 tp2 tm2
  | Just r2 <- findNumRepr tp_r1 tp2 =
    do r2_tm1 <- mrApplyRepr r2 tm1
       eq_p <- mrProveEq r2_tm1 tm2
       if eq_p then
         return (Just (tp_r1, tm1, r1, r2))
         else return Nothing

-- If there is a numeric repr r1'' from tp2 to tp_r1, then we pre-compose that
-- with r1 and use the identity for r2', assuming r1'' tm2 = tm1
injUnifyRepr tp_r1 tm1 r1 tp2 tm2
  | Just r1'' <- findNumRepr tp2 tp_r1 =
    do r1_tm2 <- mrApplyRepr r1'' tm2
       eq_p <- mrProveEq tm1 r1_tm2
       if eq_p then
         return (Just (tp2, tm2, injReprComp r1'' r1, InjReprId))
         else return Nothing

-- Otherwise, build a representation r2 for tm2, check that its representation
-- type equals tp_r1, and check that r1 tm1 is related to tm2
injUnifyRepr tp_r1 tm1 r1 tp2 tm2 =
  do (tp_r2, _, r2) <- mkInjReprTerm tp2 tm2
     tps_eq <- mrConvertible tp_r1 tp_r2
     if not tps_eq then return Nothing else
       do r1_tm1 <- mrApplyRepr r1 tm1
          rel <- mrProveEq r1_tm1 tm2
          if rel then return (Just (tp_r1, tm1, r1, r2)) else
            return Nothing


----------------------------------------------------------------------
-- * Checking Equality with SMT
----------------------------------------------------------------------

-- | Build a Boolean 'Term' stating that two 'Term's are equal. This is like
-- 'scEq' except that it works on open terms.
mrEq :: Term -> Term -> MRM t Term
mrEq t1 t2 = mrTypeOf t1 >>= \case
  (asSimpleEq -> Just eqf) -> liftSC2 eqf t1 t2
  _ -> error "mrEq: unsupported type"

-- | Recognize a nat, bool, integer, bitvector, or num type as the function
-- which builds a boolean 'Term' stating that two terms of that type are equal 
asSimpleEq :: Recognizer Term (SharedContext -> Term -> Term -> IO Term)
asSimpleEq (asNatType -> Just _) = Just $ scEqualNat
asSimpleEq (asBoolType -> Just _) = Just $ scBoolEq
asSimpleEq (asIntegerType -> Just _) = Just $ scIntEq
asSimpleEq (asSymBitvectorType -> Just n) = Just $ flip scBvEq n
asSimpleEq (asNumType -> Just ()) = Just $ \sc t1 t2 ->
  scGlobalApply sc "Cryptol.tcEqual" [t1, t2]
asSimpleEq _ = Nothing

-- | A 'Term' in an extended context of universal variables, which are listed
-- \"outside in\", meaning the highest deBruijn index comes first
data TermInCtx = TermInCtx [(LocalName,Term)] Term

-- | Lift a binary operation on 'Term's to one on 'TermInCtx's
liftTermInCtx2 :: (SharedContext -> Term -> Term -> IO Term) ->
                   TermInCtx -> TermInCtx -> MRM t TermInCtx
liftTermInCtx2 op (TermInCtx ctx1 t1) (TermInCtx ctx2 t2) =
  do
    -- Insert the variables in ctx2 into the context of t1 starting at index 0,
    -- by lifting its variables starting at 0 by length ctx2
    t1' <- liftTermLike 0 (length ctx2) t1
    -- Insert the variables in ctx1 into the context of t1 starting at index
    -- length ctx2, by lifting its variables starting at length ctx2 by length
    -- ctx1
    t2' <- liftTermLike (length ctx2) (length ctx1) t2
    TermInCtx (ctx1++ctx2) <$> liftSC2 op t1' t2'

-- | Extend the context of a 'TermInCtx' with additional universal variables
-- bound \"outside\" the 'TermInCtx'
extTermInCtx :: [(LocalName,Term)] -> TermInCtx -> TermInCtx
extTermInCtx ctx (TermInCtx ctx' t) = TermInCtx (ctx++ctx') t

-- | Run an 'MRM t' computation in the context of a 'TermInCtx', passing in the
-- 'Term'
withTermInCtx :: TermInCtx -> (Term -> MRM t a) -> MRM t a
withTermInCtx (TermInCtx [] tm) f = f tm
withTermInCtx (TermInCtx ((nm,tp):ctx) tm) f =
  withUVar nm (Type tp) $ const $ withTermInCtx (TermInCtx ctx tm) f

-- | Prove that two terms are equal, returning true on success and instantiating
-- evars if necessary - the same as @mrProveRel Nothing@
mrProveEq :: Term -> Term -> MRM t Bool
mrProveEq = mrProveRel Nothing

-- | Prove that two terms are equal, throwing an error if this is not possible
-- and instantiating evars if necessary - the same as @mrAssertProveRel Nothing@
mrAssertProveEq :: Term -> Term -> MRM t ()
mrAssertProveEq = mrAssertProveRel Nothing

-- | A relation over two terms, the second and fourth arguments, and their
-- respective types, the first and third arguments
type MRRel t a = Term -> Term -> Term -> Term -> MRM t a

-- | Prove that two terms are related via a relation, if given, on terms of
-- SpecFun type (as in 'isSpecFunType') or via equality otherwise, returning
-- false if this is not possible and instantiating evars if necessary
mrProveRel :: Maybe (MRRel t ()) -> Term -> Term -> MRM t Bool
mrProveRel piRel t1 t2 = mrProveRelH piRel t1 t2 >>= \case
  Left err -> mrDebugPPPrefix 2 "mrProveRel Failure:" err >> return False
  Right res -> do
    mrDebugPrint 2 $ "mrProveRel: " ++ if res then "Success" else "Failure"
    return res

-- | Prove that two terms are related via a relation, if given, on terms of
-- SpecFun type (as in 'isSpecFunType') or via equality otherwise, throwing an
-- error if this is not possible and instantiating evars if necessary
mrAssertProveRel :: Maybe (MRRel t ()) -> Term -> Term -> MRM t ()
mrAssertProveRel piRel t1 t2 = mrProveRelH piRel t1 t2 >>= \case
  Left err -> throwMRFailure (MRFailureCtx (FailCtxProveRel t1 t2) err)
  Right success -> unless success $ throwMRFailure (TermsNotEq t1 t2)

-- | The implementation of 'mrProveRel' and 'mrAssertProveRel'
mrProveRelH :: Maybe (MRRel t ()) -> Term -> Term -> MRM t (Either MRFailure Bool)
mrProveRelH piRel t1 t2 =
  do mrDebugPPPrefixSep 2 "mrProveRel" t1 "~=" t2
     tp1 <- mrTypeOf t1 >>= mrSubstEVars
     tp2 <- mrTypeOf t2 >>= mrSubstEVars
     ts_eq <- mrConvertible t1 t2
     if ts_eq then return $ Right True
     else mrRelTerm piRel tp1 t1 tp2 t2 >>=
          mapM (\cond_in_ctx -> withTermInCtx cond_in_ctx mrProvable)

-- | The main workhorse for 'mrProveRel' and 'mrProveRel': build a Boolean term
-- over zero or more universally quantified variables expressing that the two
-- given terms of the two given types are related
mrRelTerm :: Maybe (MRRel t ()) -> MRRel t (Either MRFailure TermInCtx)
mrRelTerm piRel tp1 t1 tp2 t2 =
  do varmap <- mrVars
     tp1' <- liftSC1 scWhnf tp1
     tp2' <- liftSC1 scWhnf tp2
     mrRelTerm' varmap piRel tp1' t1 tp2' t2

-- | The body of 'mrRelTerm'
-- NOTE: Don't call this function recursively, call 'mrRelTerm'
mrRelTerm' :: Map MRVar MRVarInfo -> Maybe (MRRel t ()) ->
              MRRel t (Either MRFailure TermInCtx)

-- If t1 is an instantiated evar, substitute and recurse
mrRelTerm' var_map piRel tp1 (asEVarApp var_map -> Just (_, _, args, Just f)) tp2 t2 =
  mrApplyAll f args >>= \t1' -> mrRelTerm piRel tp1 t1' tp2 t2

-- If t1 is an uninstantiated evar, ensure the types are equal and instantiate
-- it with t2
mrRelTerm' var_map _ tp1 (asEVarApp var_map -> Just (evar, _, args, Nothing)) tp2 t2 =
  do tps_are_eq <- mrConvertible tp1 tp2
     unless tps_are_eq $ throwMRFailure (TypesNotEq (Type tp1) (Type tp2))
     t2' <- mrSubstEVars t2
     success <- mrTrySetAppliedEVar evar args t2'
     when success $
       mrDebugPPPrefixSep 1 "setting evar" evar "to" t2
     Right <$> TermInCtx [] <$> liftSC1 scBool success

-- If t2 is an instantiated evar, substitute and recurse
mrRelTerm' var_map piRel tp1 t1 tp2 (asEVarApp var_map -> Just (_, _, args, Just f)) =
  mrApplyAll f args >>= \t2' -> mrRelTerm piRel tp1 t1 tp2 t2'

-- If t2 is an uninstantiated evar, ensure the types are equal and instantiate
-- it with t1
mrRelTerm' var_map _ tp1 t1 tp2 (asEVarApp var_map -> Just (evar, _, args, Nothing)) =
  do tps_are_eq <- mrConvertible tp1 tp2
     unless tps_are_eq $ throwMRFailure (TypesNotEq (Type tp1) (Type tp2))
     t1' <- mrSubstEVars t1
     success <- mrTrySetAppliedEVar evar args t1'
     when success $
       mrDebugPPPrefixSep 1 "setting evar" evar "to" t1
     Right <$> TermInCtx [] <$> liftSC1 scBool success

-- For unit types, always return true
mrRelTerm' _ _ (asTupleType -> Just []) _ (asTupleType -> Just []) _ =
  Right <$> TermInCtx [] <$> liftSC1 scBool True

-- For nat, bool, integer, bitvector, or num type types, use asSimpleEq
mrRelTerm' _ _ tp1@(asSimpleEq -> Just eqf) t1 tp2 t2 =
  do tps_are_eq <- mrConvertible tp1 tp2
     unless tps_are_eq $ throwMRFailure (TypesNotEq (Type tp1) (Type tp2))
     t1' <- mrSubstEVars t1
     t2' <- mrSubstEVars t2
     Right <$> TermInCtx [] <$> liftSC2 eqf t1' t2'

-- For BVVec types, prove all projections are related by quantifying over an
-- index variable and proving the projections at that index are related
mrRelTerm' _ piRel tp1@(asVecTypeWithLen -> Just (vlen1, tpA1)) t1
                   tp2@(asVecTypeWithLen -> Just (vlen2, tpA2)) t2 =
  mrVecLenUnify vlen1 vlen2 >>= \case
    Just (vlen1', vlen2') ->
      mrVecLenIxType vlen1' >>= \ix_tp ->
      withUVarLift "ix" (Type ix_tp) (vlen1',vlen2',tpA1,tpA2,t1,t2) $
      \ix (vlen1'',vlen2'',tpA1',tpA2',t1',t2') ->
      do ix_bound <- mrVecLenIxBound vlen1'' ix
         t1_prj <- mrVecLenAt vlen1'' tpA1' t1' ix
         t2_prj <- mrVecLenAt vlen2'' tpA2' t2' ix
         mrRelTerm piRel tpA1' t1_prj tpA2' t2_prj >>= mapM (\cond ->
          extTermInCtx [("ix",ix_tp)] <$>
            liftTermInCtx2 scImplies (TermInCtx [] ix_bound) cond)
    Nothing -> throwMRFailure (TypesNotEq (Type tp1) (Type tp2))

-- For pair types, prove both the left and right projections are related
-- FIXME: Don't re-associate tuples
mrRelTerm' _ piRel (asPairType -> Just (asPairType -> Just (tp1a, tp1b), tp1c)) t1
                   tp2 t2 =
  do tp1' <- liftSC2 scPairType tp1a =<< liftSC2 scPairType tp1b tp1c
     mrRelTerm piRel tp1' t1 tp2 t2
mrRelTerm' _ piRel tp1 t1
                   (asPairType -> Just (asPairType -> Just (tp2a, tp2b), tp2c)) t2 =
  do tp2' <- liftSC2 scPairType tp2a =<< liftSC2 scPairType tp2b tp2c
     mrRelTerm piRel tp1 t1 tp2' t2
mrRelTerm' _ piRel (asPairType -> Just (tpL1, tpR1)) t1
                   (asPairType -> Just (tpL2, tpR2)) t2 =
  do t1L <- liftSC1 scPairLeft t1
     t2L <- liftSC1 scPairLeft t2
     t1R <- liftSC1 scPairRight t1
     t2R <- liftSC1 scPairRight t2
     mb_condL <- mrRelTerm piRel tpL1 t1L tpL2 t2L
     mb_condR <- mrRelTerm piRel tpR1 t1R tpR2 t2R
     sequence $ liftTermInCtx2 scAnd <$> mb_condL <*> mb_condR

mrRelTerm' _ piRel tp1 t1 tp2 t2 =
  mrSC >>= \sc ->
  liftIO (isSpecFunType sc tp1) >>= \tp1_is_specFun ->
  liftIO (isSpecFunType sc tp2) >>= \tp2_is_specFun ->
  case piRel of
    -- If given a relation, on terms of SpecFun type return True iff the
    -- relation returns without raising a 'MRFailure'
    Just piRel' | tp1_is_specFun, tp2_is_specFun ->
      (piRel' tp1 t1 tp2 t2 >> Right <$> TermInCtx [] <$> liftSC1 scBool True)
        `catchFailure` \err -> return $ Left err
    -- Otherwise, return True iff the terms are convertible
    _ -> do
      tps_are_eq <- mrConvertible tp1 tp2
      unless tps_are_eq $ throwMRFailure (TypesNotEq (Type tp1) (Type tp2))
      tms_are_eq <- mrConvertible t1 t2
      if tms_are_eq then Right <$> TermInCtx [] <$> liftSC1 scBool True
                    else return $ Left $ TermsNotEq t1 t2
