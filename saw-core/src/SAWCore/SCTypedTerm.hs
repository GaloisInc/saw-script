{- |
Module      : SAWCore.SCTypedTerm
Copyright   : Galois, Inc. 2025
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module SAWCore.SCTypedTerm
  ( SCTypedTerm -- abstract
  , typedVal
  , typedType
  , typedCtx
  , scTypeCheckWHNF
  , scTypeOfTypedTerm
  , scTypedTermWHNF
  , scGlobalTypedTerm
    -- * Building typed terms
  , scTypedApply
  , scTypedLambda
  , scTypedPi
  , scTypedFun
  , scTypedConstant
  , scTypedVariable
  , scTypedUnitValue
  , scTypedUnitType
  , scTypedPairValue
  , scTypedPairType
  , scTypedPairLeft
  , scTypedPairRight
  , scTypedRecursor
  , scTypedRecordType
  , scTypedRecordValue
  , scTypedRecordProj
  , scTypedSort
  , scTypedSort'
  , scTypedNat
  , scTypedVector
  , scTypedString
  ) where

import Control.Monad (foldM, unless, when)
import qualified Data.Foldable as Fold
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text)
import Numeric.Natural (Natural)

import SAWCore.Conversion (natConversions)
import SAWCore.Module (Ctor(..), DataType(..), ResolvedName(..), lookupVarIndexInMap)
import SAWCore.Name
import SAWCore.Recognizer
import SAWCore.Rewriter
import SAWCore.SharedTerm
import SAWCore.Term.Functor
import SAWCore.Term.Pretty (showTerm)

--------------------------------------------------------------------------------
-- * Certified typed terms

-- | An abstract datatype pairing a well-formed 'Term' with its type.
data SCTypedTerm =
  SCTypedTerm
  Term -- ^ value
  Term -- ^ type
  (IntMap Term) -- ^ typing context

-- | The raw 'Term' of an 'SCTypedTerm'.
typedVal :: SCTypedTerm -> Term
typedVal (SCTypedTerm trm _ _) = trm

-- | The type of an 'SCTypedTerm' as a 'Term'.
typedType :: SCTypedTerm -> Term
typedType (SCTypedTerm _ typ _) = typ

-- | The typing context of an 'SCTypedTerm', keyed by the 'VarIndex'
-- of each 'VarName' in the term.
typedCtx :: SCTypedTerm -> IntMap Term
typedCtx (SCTypedTerm _ _ ctx) = ctx

-- | Reduce the given 'Term' to WHNF, using all reductions allowed by
-- the SAWCore type system.
scTypeCheckWHNF :: SharedContext -> Term -> IO Term
scTypeCheckWHNF sc t =
  do (_, t') <- rewriteSharedTerm sc (addConvs natConversions emptySimpset :: Simpset ()) t
     scWhnf sc t'

-- | Check if two terms are "convertible for type-checking", meaning that they
-- are convertible up to 'natConversions'.
scTypeConvertible :: SharedContext -> Term -> Term -> IO Bool
scTypeConvertible sc t1 t2 = scConvertibleEval sc scTypeCheckWHNF True t1 t2

-- | Check whether one type is a subtype of another: Either they are
-- convertible, or they are both Pi types with convertible argument
-- types and result sorts @s1@ and @s2@ with @s1 <= s2@.
scSubtype :: SharedContext -> Term -> Term -> IO Bool
scSubtype sc t1 t2
  | alphaEquiv t1 t2 = pure True
  | otherwise =
    do t1' <- scWhnf sc t1
       t2' <- scWhnf sc t2
       case (t1', t2') of
         (asSort -> Just s1, asSort -> Just s2) ->
           pure (s1 <= s2)
         (unwrapTermF -> Pi x1 a1 b1, unwrapTermF -> Pi x2 a2 b2)
           | x1 == x2 ->
             (&&) <$> scTypeConvertible sc a1 a2 <*> scSubtype sc b1 b2
           | otherwise ->
             do conv1 <- scTypeConvertible sc a1 a2
                var1 <- scVariable sc (EC x1 a1)
                b2' <- scInstantiateExt sc (IntMap.singleton (vnIndex x2) var1) b2
                conv2 <- scSubtype sc b1 b2'
                pure (conv1 && conv2)
         _ ->
           scTypeConvertible sc t1' t2'

--------------------------------------------------------------------------------
-- * Operations on typed terms

-- | Compute the type of an 'SCTypedTerm'.
scTypeOfTypedTerm :: SharedContext -> SCTypedTerm -> IO SCTypedTerm
scTypeOfTypedTerm sc (SCTypedTerm _tm tp ctx) =
  do tp_tp <- scTypeOf' sc ctx tp
     -- Shrink typing context if possible
     let ctx' = pruneContext (freeVars tp_tp) ctx
     pure (SCTypedTerm tp tp_tp ctx')

-- | Reduce an 'SCTypedTerm' to WHNF (see also 'scTypeCheckWHNF').
scTypedTermWHNF :: SharedContext -> SCTypedTerm -> IO SCTypedTerm
scTypedTermWHNF sc (SCTypedTerm tm tp ctx) =
  do tm' <- scTypeCheckWHNF sc tm
     pure (SCTypedTerm tm' tp ctx)

scGlobalTypedTerm :: SharedContext -> Ident -> IO SCTypedTerm
scGlobalTypedTerm sc ident =
  do tm <- scGlobalDef sc ident
     tp <- scTypeOfIdent sc ident
     pure (SCTypedTerm tm tp IntMap.empty)

--------------------------------------------------------------------------------
-- * Building typed terms

-- possible errors: not a pi type, bad argument type, context mismatch
scTypedApply :: SharedContext -> SCTypedTerm -> SCTypedTerm -> IO SCTypedTerm
scTypedApply sc f arg =
  do tm <- scApply sc (typedVal f) (typedVal arg)
     (vnIndex -> i, t1, t2) <- ensurePi sc (typedType f)
     ok <- scSubtype sc (typedType arg) t1
     unless ok $ fail $ unlines $
       ["Not a subtype", "expected: " ++ showTerm t1, "got: " ++ showTerm (typedType arg)]
     tp <- scInstantiateExt sc (IntMap.singleton i (typedVal arg)) t2
     ctx <- unifyContexts "scTypedApply" (typedCtx f) (typedCtx arg)
     pure (SCTypedTerm tm tp ctx)

-- possible errors: not a type, context mismatch, variable free in context
scTypedLambda :: SharedContext -> VarName -> SCTypedTerm -> SCTypedTerm -> IO SCTypedTerm
scTypedLambda sc x t body =
  do _s <- ensureSort sc (typedType t)
     tm <- scLambda sc x (typedVal t) (typedVal body)
     ensureNotFreeInContext x body
     _ <- unifyContexts "scTypedLambda" (IntMap.singleton (vnIndex x) (typedVal t)) (typedCtx body)
     ctx <- unifyContexts "scTypedLambda" (typedCtx t) (IntMap.delete (vnIndex x) (typedCtx body))
     tp <- scPi sc x (typedVal t) (typedType body)
     pure (SCTypedTerm tm tp ctx)

-- possible errors: not a type, context mismatch, variable free in context
scTypedPi :: SharedContext -> VarName -> SCTypedTerm -> SCTypedTerm -> IO SCTypedTerm
scTypedPi sc x t body =
  do tm <- scPi sc x (typedVal t) (typedVal body)
     ensureNotFreeInContext x body
     _ <- unifyContexts "scTypedPi" (IntMap.singleton (vnIndex x) (typedVal t)) (typedCtx body)
     ctx <- unifyContexts "scTypedPi" (typedCtx t) (IntMap.delete (vnIndex x) (typedCtx body))
     s1 <- ensureSort sc (typedType t)
     s2 <- ensureSort sc (typedType body)
     tp <- scSort sc (piSort s1 s2)
     pure (SCTypedTerm tm tp ctx)

-- possible errors: not a type, context mismatch
scTypedFun :: SharedContext -> SCTypedTerm -> SCTypedTerm -> IO SCTypedTerm
scTypedFun sc a b =
  do tm <- scFun sc (typedVal a) (typedVal b)
     sa <- ensureSort sc (typedType a)
     sb <- ensureSort sc (typedType b)
     tp <- scSort sc (piSort sa sb)
     ctx <- unifyContexts "scTypedFun" (typedCtx a) (typedCtx b)
     pure (SCTypedTerm tm tp ctx)

-- possible errors: constant not defined
scTypedConstant :: SharedContext -> Name -> IO SCTypedTerm
scTypedConstant sc nm =
  do tm <- scConst sc nm
     tp <- scTypeOfName sc nm
     pure (SCTypedTerm tm tp IntMap.empty)

-- possible errors: not a type
scTypedVariable :: SharedContext -> VarName -> SCTypedTerm -> IO SCTypedTerm
scTypedVariable sc vn t =
  do let tp = typedVal t
     tm <- scVariable sc (EC vn tp)
     let ctx = IntMap.insert (vnIndex vn) tp (typedCtx t)
     pure (SCTypedTerm tm tp ctx)

-- possible errors: none
scTypedUnitValue :: SharedContext -> IO SCTypedTerm
scTypedUnitValue sc =
  do tm <- scUnitValue sc
     tp <- scUnitType sc
     pure (SCTypedTerm tm tp IntMap.empty)

-- possible errors: none
scTypedUnitType :: SharedContext -> IO SCTypedTerm
scTypedUnitType sc =
  do tm <- scUnitType sc
     tp <- scSort sc (mkSort 0)
     pure (SCTypedTerm tm tp IntMap.empty)

-- possible errors: none (could redesign to require types in sort 0)
scTypedPairValue :: SharedContext -> SCTypedTerm -> SCTypedTerm -> IO SCTypedTerm
scTypedPairValue sc x y =
  do tm <- scPairValue sc (typedVal x) (typedVal y)
     tp <- scPairType sc (typedType x) (typedType y)
     ctx <- unifyContexts "scTypedPairValue" (typedCtx x) (typedCtx y)
     pure (SCTypedTerm tm tp ctx)

-- possible errors: not a type
scTypedPairType :: SharedContext -> SCTypedTerm -> SCTypedTerm -> IO SCTypedTerm
scTypedPairType sc x y =
  do tm <- scPairType sc (typedVal x) (typedVal y)
     sx <- ensureSort sc (typedType x)
     sy <- ensureSort sc (typedType y)
     tp <- scSort sc (max sx sy)
     ctx <- unifyContexts "scTypedPairType" (typedCtx x) (typedCtx y)
     pure (SCTypedTerm tm tp ctx)

-- possible errors: not a pair
scTypedPairLeft :: SharedContext -> SCTypedTerm -> IO SCTypedTerm
scTypedPairLeft sc x =
  do tm <- scPairLeft sc (typedVal x)
     tp <- fst <$> ensurePairType sc (typedType x)
     let ctx = typedCtx x
     pure (SCTypedTerm tm tp ctx)

-- possible errors: not a pair
scTypedPairRight :: SharedContext -> SCTypedTerm -> IO SCTypedTerm
scTypedPairRight sc x =
  do tm <- scPairRight sc (typedVal x)
     tp <- snd <$> ensurePairType sc (typedType x)
     let ctx = typedCtx x
     pure (SCTypedTerm tm tp ctx)

-- possible errors: not a datatype, bad elimination sort
scTypedRecursor :: SharedContext -> Name -> Sort -> IO SCTypedTerm
scTypedRecursor sc nm s =
  do mm <- scGetModuleMap sc
     case lookupVarIndexInMap (nameIndex nm) mm of
       Just (ResolvedDataType dt) ->
         do unless (allowedElimSort dt s) $ fail "Disallowed propositional elimination"
            let d = dtName dt
            let nparams = length (dtParams dt)
            let nixs = length (dtIndices dt)
            let ctorOrder = map ctorName (dtCtors dt)
            let crec = CompiledRecursor d s nparams nixs ctorOrder
            tm <- scFlatTermF sc (Recursor crec)
            tp <- scRecursorType sc dt s
            pure (SCTypedTerm tm tp IntMap.empty)
       _ ->
         fail "datatype not found"

-- possible errors: field not a type, context mismatch
scTypedRecordType :: SharedContext -> [(FieldName, SCTypedTerm)] -> IO SCTypedTerm
scTypedRecordType sc fields =
  do tm <- scRecordType sc (map (fmap typedVal) fields)
     sorts <- traverse (ensureSort sc . typedType . snd) fields
     tp <- scSort sc (foldl max (mkSort 0) sorts)
     ctx <- unifyContextList "scTypedRecordType" (map (typedCtx . snd) fields)
     pure (SCTypedTerm tm tp ctx)

-- possible errors: duplicate field name
scTypedRecordValue :: SharedContext -> [(FieldName, SCTypedTerm)] -> IO SCTypedTerm
scTypedRecordValue sc fields =
  do tm <- scFlatTermF sc $ RecordValue (map (fmap typedVal) fields)
     tp <- scRecordType sc (map (fmap typedType) fields)
     ctx <- foldM (unifyContexts "scTypedRecordValue") IntMap.empty (map (typedCtx . snd) fields)
     pure (SCTypedTerm tm tp ctx)

-- possible errors: not a record type, field name not found
scTypedRecordProj :: SharedContext -> SCTypedTerm -> FieldName -> IO SCTypedTerm
scTypedRecordProj sc t fname =
  do tm <- scRecordSelect sc (typedVal t) fname
     let ctx = typedCtx t
     tps <- ensureRecordType sc (typedType t)
     case Map.lookup fname tps of
       Nothing -> fail "scTypedRecordProj: field name not found"
       Just tp -> pure (SCTypedTerm tm tp ctx)

-- no possible errors
scTypedSort :: SharedContext -> Sort -> IO SCTypedTerm
scTypedSort sc s = scTypedSort' sc s noFlags

-- | A variant of 'scTypedSort' that also takes a 'SortFlags' argument.
-- No possible errors.
scTypedSort' :: SharedContext -> Sort -> SortFlags -> IO SCTypedTerm
scTypedSort' sc s flags =
  do tm <- scFlatTermF sc (Sort s flags)
     tp <- scSort sc (sortOf s)
     pure (SCTypedTerm tm tp IntMap.empty)

-- no possible errors
scTypedNat :: SharedContext -> Natural -> IO SCTypedTerm
scTypedNat sc n =
  do tm <- scNat sc n
     tp <- scNatType sc
     pure (SCTypedTerm tm tp IntMap.empty)

-- possible errors: context mismatch, element type not a type, element wrong type
scTypedVector :: SharedContext -> SCTypedTerm -> [SCTypedTerm] -> IO SCTypedTerm
scTypedVector sc e xs =
  do -- TODO: check that all xs have type e
     tm <- scVector sc (typedVal e) (map typedVal xs)
     n <- scNat sc (fromIntegral (length xs))
     tp <- scVecType sc n (typedVal e)
     ctx <- foldM (unifyContexts "scTypedVector") (typedCtx e) (map typedCtx xs)
     pure (SCTypedTerm tm tp ctx)

-- no possible errors
scTypedString :: SharedContext -> Text -> IO SCTypedTerm
scTypedString sc s =
  do tm <- scString sc s
     tp <- scStringType sc
     pure (SCTypedTerm tm tp IntMap.empty)

--------------------------------------------------------------------------------
-- * Utility functions

-- | Prune a typing context by dropping indices unreachable from the
-- given 'IntSet'.
pruneContext :: IntSet -> IntMap Term -> IntMap Term
pruneContext vs0 ctx = IntMap.restrictKeys ctx (reachable mempty vs0)
  where
    fvs = fmap freeVars ctx
    reachable old new
      | IntSet.null new = old
      | otherwise = reachable old' new'
          where old' = old <> new
                new' = IntSet.difference (Fold.fold (IntMap.restrictKeys fvs new)) old'

-- | Two typing contexts are unifiable if they agree perfectly on all
-- entries where they overlap.
unifyContexts :: String -> IntMap Term -> IntMap Term -> IO (IntMap Term)
unifyContexts msg ctx1 ctx2 =
  do let check t1 t2 =
           unless (t1 == t2) $
           fail $ unlines ["unifyContexts: context mismatch", msg,
                           "t1: " ++ showTerm t1,
                           "t2: " ++ showTerm t2]
     sequence_ (IntMap.intersectionWith check ctx1 ctx2)
     pure (IntMap.union ctx1 ctx2)

unifyContextList :: String -> [IntMap Term] -> IO (IntMap Term)
unifyContextList msg = foldM (unifyContexts msg) IntMap.empty

ensureRecognizer :: String -> SharedContext -> (Term -> Maybe a) -> Term -> IO a
ensureRecognizer s sc f trm =
  case f trm of
    Just a -> pure a
    Nothing ->
      do trm' <- scTypeCheckWHNF sc trm
         case f trm' of
           Just a -> pure a
           Nothing ->
             fail $ "ensureRecognizer: Expected " ++ s ++ ", found: " ++ showTerm trm'

ensureSort :: SharedContext -> Term -> IO Sort
ensureSort sc tp = ensureRecognizer "Sort" sc asSort tp

ensurePi :: SharedContext -> Term -> IO (VarName, Term, Term)
ensurePi sc tp = ensureRecognizer "Pi" sc asPi tp

ensurePairType :: SharedContext -> Term -> IO (Term, Term)
ensurePairType sc tp = ensureRecognizer "PairType" sc asPairType tp

ensureRecordType :: SharedContext -> Term -> IO (Map FieldName Term)
ensureRecordType sc tp = ensureRecognizer "RecordType" sc asRecordType tp

piSort :: Sort -> Sort -> Sort
piSort s1 s2 = if s2 == propSort then propSort else max s1 s2

-- | Check whether the given 'VarName' occurs free in the type of
-- another variable in the context of the given 'SCTypedTerm', and
-- fail if it does.
ensureNotFreeInContext :: VarName -> SCTypedTerm -> IO ()
ensureNotFreeInContext x body =
  when (any (IntSet.member (vnIndex x) . freeVars) (typedCtx body)) $
    fail $ "Variable occurs free in context: " ++ show (vnName x)
