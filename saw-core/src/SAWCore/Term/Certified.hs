{- |
Module      : SAWCore.Term.Certified
Copyright   : Galois, Inc. 2025
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module SAWCore.Term.Certified
  ( Term -- abstract
  , rawTerm
  , rawType
  , rawCtx
  , scTypeCheckWHNF
  , scTypeOf
  , scWHNF
    -- * Building certified terms
  , scApply
  , scLambda
  , scPi
  , scFun
  , scConstant
  , scGlobal
  , scVariable
  , scUnitValue
  , scUnitType
  , scPairValue
  , scPairType
  , scPairLeft
  , scPairRight
  , scRecursor
  , scRecordType
  , scRecordValue
  , scRecordProj
  , scSort
  , scSort'
  , scNat
  , scVector
  , scString
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
import SAWCore.SharedTerm (SharedContext)
import qualified SAWCore.SharedTerm as Raw
import SAWCore.Term.Functor
import SAWCore.Term.Pretty (showTerm)
import SAWCore.Term.Raw (alphaEquiv, freeVars, unwrapTermF)

--------------------------------------------------------------------------------
-- * Certified typed terms

-- | An abstract datatype pairing a well-formed 'Raw.Term' with its type.
data Term =
  Term
  Raw.Term -- ^ value
  Raw.Term -- ^ type
  (IntMap Raw.Term) -- ^ typing context

-- | The raw term of a 'Term'.
rawTerm :: Term -> Raw.Term
rawTerm (Term trm _ _) = trm

-- | The type of a 'Term' as a raw term.
rawType :: Term -> Raw.Term
rawType (Term _ typ _) = typ

-- | The typing context of a 'Term', keyed by the 'VarIndex' of each
-- 'VarName' in the term.
rawCtx :: Term -> IntMap Raw.Term
rawCtx (Term _ _ ctx) = ctx

-- | Reduce the given 'Raw.Term' to WHNF, using all reductions allowed by
-- the SAWCore type system.
scTypeCheckWHNF :: SharedContext -> Raw.Term -> IO Raw.Term
scTypeCheckWHNF sc t =
  do (_, t') <- rewriteSharedTerm sc (addConvs natConversions emptySimpset :: Simpset ()) t
     Raw.scWhnf sc t'

-- | Check if two terms are "convertible for type-checking", meaning that they
-- are convertible up to 'natConversions'.
scTypeConvertible :: SharedContext -> Raw.Term -> Raw.Term -> IO Bool
scTypeConvertible sc t1 t2 = Raw.scConvertibleEval sc scTypeCheckWHNF True t1 t2

-- | Check whether one type is a subtype of another: Either they are
-- convertible, or they are both Pi types with convertible argument
-- types and result sorts @s1@ and @s2@ with @s1 <= s2@.
scSubtype :: SharedContext -> Raw.Term -> Raw.Term -> IO Bool
scSubtype sc t1 t2
  | alphaEquiv t1 t2 = pure True
  | otherwise =
    do t1' <- Raw.scWhnf sc t1
       t2' <- Raw.scWhnf sc t2
       case (t1', t2') of
         (asSort -> Just s1, asSort -> Just s2) ->
           pure (s1 <= s2)
         (unwrapTermF -> Pi x1 a1 b1, unwrapTermF -> Pi x2 a2 b2)
           | x1 == x2 ->
             (&&) <$> scTypeConvertible sc a1 a2 <*> scSubtype sc b1 b2
           | otherwise ->
             do conv1 <- scTypeConvertible sc a1 a2
                var1 <- Raw.scVariable sc x1 a1
                b2' <- Raw.scInstantiateExt sc (IntMap.singleton (vnIndex x2) var1) b2
                conv2 <- scSubtype sc b1 b2'
                pure (conv1 && conv2)
         _ ->
           scTypeConvertible sc t1' t2'

--------------------------------------------------------------------------------
-- * Operations on typed terms

-- | Compute the type of a 'Term'.
scTypeOf :: SharedContext -> Term -> IO Term
scTypeOf sc (Term _tm tp ctx) =
  do tp_tp <- Raw.scTypeOf' sc ctx tp
     -- Shrink typing context if possible
     let ctx' = pruneContext (freeVars tp_tp) ctx
     pure (Term tp tp_tp ctx')

-- | Reduce a 'Cterm' to WHNF (see also 'scTypeCheckWHNF').
scWHNF :: SharedContext -> Term -> IO Term
scWHNF sc (Term tm tp ctx) =
  do tm' <- scTypeCheckWHNF sc tm
     pure (Term tm' tp ctx)

scGlobal :: SharedContext -> Ident -> IO Term
scGlobal sc ident =
  do tm <- Raw.scGlobalDef sc ident
     tp <- Raw.scTypeOfIdent sc ident
     pure (Term tm tp IntMap.empty)

--------------------------------------------------------------------------------
-- * Building certified terms

-- possible errors: not a pi type, bad argument type, context mismatch
scApply :: SharedContext -> Term -> Term -> IO Term
scApply sc f arg =
  do tm <- Raw.scApply sc (rawTerm f) (rawTerm arg)
     (vnIndex -> i, t1, t2) <- ensurePi sc (rawType f)
     ok <- scSubtype sc (rawType arg) t1
     unless ok $ fail $ unlines $
       ["Not a subtype", "expected: " ++ showTerm t1, "got: " ++ showTerm (rawType arg)]
     tp <- Raw.scInstantiateExt sc (IntMap.singleton i (rawTerm arg)) t2
     ctx <- unifyContexts "scApply" (rawCtx f) (rawCtx arg)
     pure (Term tm tp ctx)

-- possible errors: not a type, context mismatch, variable free in context
scLambda :: SharedContext -> VarName -> Term -> Term -> IO Term
scLambda sc x t body =
  do _s <- ensureSort sc (rawType t)
     tm <- Raw.scLambda sc x (rawTerm t) (rawTerm body)
     ensureNotFreeInContext x body
     _ <- unifyContexts "scLambda" (IntMap.singleton (vnIndex x) (rawTerm t)) (rawCtx body)
     ctx <- unifyContexts "scLambda" (rawCtx t) (IntMap.delete (vnIndex x) (rawCtx body))
     tp <- Raw.scPi sc x (rawTerm t) (rawType body)
     pure (Term tm tp ctx)

-- possible errors: not a type, context mismatch, variable free in context
scPi :: SharedContext -> VarName -> Term -> Term -> IO Term
scPi sc x t body =
  do tm <- Raw.scPi sc x (rawTerm t) (rawTerm body)
     ensureNotFreeInContext x body
     _ <- unifyContexts "scTypedPi" (IntMap.singleton (vnIndex x) (rawTerm t)) (rawCtx body)
     ctx <- unifyContexts "scTypedPi" (rawCtx t) (IntMap.delete (vnIndex x) (rawCtx body))
     s1 <- ensureSort sc (rawType t)
     s2 <- ensureSort sc (rawType body)
     tp <- Raw.scSort sc (piSort s1 s2)
     pure (Term tm tp ctx)

-- possible errors: not a type, context mismatch
scFun :: SharedContext -> Term -> Term -> IO Term
scFun sc a b =
  do tm <- Raw.scFun sc (rawTerm a) (rawTerm b)
     sa <- ensureSort sc (rawType a)
     sb <- ensureSort sc (rawType b)
     tp <- Raw.scSort sc (piSort sa sb)
     ctx <- unifyContexts "scFun" (rawCtx a) (rawCtx b)
     pure (Term tm tp ctx)

-- possible errors: constant not defined
scConstant :: SharedContext -> Name -> IO Term
scConstant sc nm =
  do tm <- Raw.scConst sc nm
     tp <- Raw.scTypeOfName sc nm
     pure (Term tm tp IntMap.empty)

-- possible errors: not a type
scVariable :: SharedContext -> VarName -> Term -> IO Term
scVariable sc vn t =
  do let tp = rawTerm t
     tm <- Raw.scVariable sc vn tp
     let ctx = IntMap.insert (vnIndex vn) tp (rawCtx t)
     pure (Term tm tp ctx)

-- possible errors: none
scUnitValue :: SharedContext -> IO Term
scUnitValue sc =
  do tm <- Raw.scUnitValue sc
     tp <- Raw.scUnitType sc
     pure (Term tm tp IntMap.empty)

-- possible errors: none
scUnitType :: SharedContext -> IO Term
scUnitType sc =
  do tm <- Raw.scUnitType sc
     tp <- Raw.scSort sc (mkSort 0)
     pure (Term tm tp IntMap.empty)

-- possible errors: none (could redesign to require types in sort 0)
scPairValue :: SharedContext -> Term -> Term -> IO Term
scPairValue sc x y =
  do tm <- Raw.scPairValue sc (rawTerm x) (rawTerm y)
     tp <- Raw.scPairType sc (rawType x) (rawType y)
     ctx <- unifyContexts "scPairValue" (rawCtx x) (rawCtx y)
     pure (Term tm tp ctx)

-- possible errors: not a type
scPairType :: SharedContext -> Term -> Term -> IO Term
scPairType sc x y =
  do tm <- Raw.scPairType sc (rawTerm x) (rawTerm y)
     sx <- ensureSort sc (rawType x)
     sy <- ensureSort sc (rawType y)
     tp <- Raw.scSort sc (max sx sy)
     ctx <- unifyContexts "scPairType" (rawCtx x) (rawCtx y)
     pure (Term tm tp ctx)

-- possible errors: not a pair
scPairLeft :: SharedContext -> Term -> IO Term
scPairLeft sc x =
  do tm <- Raw.scPairLeft sc (rawTerm x)
     tp <- fst <$> ensurePairType sc (rawType x)
     let ctx = rawCtx x
     pure (Term tm tp ctx)

-- possible errors: not a pair
scPairRight :: SharedContext -> Term -> IO Term
scPairRight sc x =
  do tm <- Raw.scPairRight sc (rawTerm x)
     tp <- snd <$> ensurePairType sc (rawType x)
     let ctx = rawCtx x
     pure (Term tm tp ctx)

-- possible errors: not a datatype, bad elimination sort
scRecursor :: SharedContext -> Name -> Sort -> IO Term
scRecursor sc nm s =
  do mm <- Raw.scGetModuleMap sc
     case lookupVarIndexInMap (nameIndex nm) mm of
       Just (ResolvedDataType dt) ->
         do unless (Raw.allowedElimSort dt s) $ fail "Disallowed propositional elimination"
            let d = dtName dt
            let nparams = length (dtParams dt)
            let nixs = length (dtIndices dt)
            let ctorOrder = map ctorName (dtCtors dt)
            let crec = CompiledRecursor d s nparams nixs ctorOrder
            tm <- Raw.scFlatTermF sc (Recursor crec)
            tp <- Raw.scRecursorType sc dt s
            pure (Term tm tp IntMap.empty)
       _ ->
         fail "datatype not found"

-- possible errors: field not a type, context mismatch
scRecordType :: SharedContext -> [(FieldName, Term)] -> IO Term
scRecordType sc fields =
  do tm <- Raw.scRecordType sc (map (fmap rawTerm) fields)
     sorts <- traverse (ensureSort sc . rawType . snd) fields
     tp <- Raw.scSort sc (foldl max (mkSort 0) sorts)
     ctx <- unifyContextList "scRecordType" (map (rawCtx . snd) fields)
     pure (Term tm tp ctx)

-- possible errors: duplicate field name
scRecordValue :: SharedContext -> [(FieldName, Term)] -> IO Term
scRecordValue sc fields =
  do tm <- Raw.scFlatTermF sc $ RecordValue (map (fmap rawTerm) fields)
     tp <- Raw.scRecordType sc (map (fmap rawType) fields)
     ctx <- foldM (unifyContexts "scRecordValue") IntMap.empty (map (rawCtx . snd) fields)
     pure (Term tm tp ctx)

-- possible errors: not a record type, field name not found
scRecordProj :: SharedContext -> Term -> FieldName -> IO Term
scRecordProj sc t fname =
  do tm <- Raw.scRecordSelect sc (rawTerm t) fname
     let ctx = rawCtx t
     tps <- ensureRecordType sc (rawType t)
     case Map.lookup fname tps of
       Nothing -> fail "scRecordProj: field name not found"
       Just tp -> pure (Term tm tp ctx)

-- no possible errors
scSort :: SharedContext -> Sort -> IO Term
scSort sc s = scSort' sc s noFlags

-- | A variant of 'scSort' that also takes a 'SortFlags' argument.
-- No possible errors.
scSort' :: SharedContext -> Sort -> SortFlags -> IO Term
scSort' sc s flags =
  do tm <- Raw.scFlatTermF sc (Sort s flags)
     tp <- Raw.scSort sc (sortOf s)
     pure (Term tm tp IntMap.empty)

-- no possible errors
scNat :: SharedContext -> Natural -> IO Term
scNat sc n =
  do tm <- Raw.scNat sc n
     tp <- Raw.scNatType sc
     pure (Term tm tp IntMap.empty)

-- possible errors: context mismatch, element type not a type, element wrong type
scVector :: SharedContext -> Term -> [Term] -> IO Term
scVector sc e xs =
  do -- TODO: check that all xs have type e
     tm <- Raw.scVector sc (rawTerm e) (map rawTerm xs)
     n <- Raw.scNat sc (fromIntegral (length xs))
     tp <- Raw.scVecType sc n (rawTerm e)
     ctx <- foldM (unifyContexts "scVector") (rawCtx e) (map rawCtx xs)
     pure (Term tm tp ctx)

-- no possible errors
scString :: SharedContext -> Text -> IO Term
scString sc s =
  do tm <- Raw.scString sc s
     tp <- Raw.scStringType sc
     pure (Term tm tp IntMap.empty)

--------------------------------------------------------------------------------
-- * Utility functions

-- | Prune a typing context by dropping indices unreachable from the
-- given 'IntSet'.
pruneContext :: IntSet -> IntMap Raw.Term -> IntMap Raw.Term
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
unifyContexts :: String -> IntMap Raw.Term -> IntMap Raw.Term -> IO (IntMap Raw.Term)
unifyContexts msg ctx1 ctx2 =
  do let check t1 t2 =
           unless (t1 == t2) $
           fail $ unlines ["unifyContexts: context mismatch", msg,
                           "t1: " ++ showTerm t1,
                           "t2: " ++ showTerm t2]
     sequence_ (IntMap.intersectionWith check ctx1 ctx2)
     pure (IntMap.union ctx1 ctx2)

unifyContextList :: String -> [IntMap Raw.Term] -> IO (IntMap Raw.Term)
unifyContextList msg = foldM (unifyContexts msg) IntMap.empty

ensureRecognizer :: String -> SharedContext -> (Raw.Term -> Maybe a) -> Raw.Term -> IO a
ensureRecognizer s sc f trm =
  case f trm of
    Just a -> pure a
    Nothing ->
      do trm' <- scTypeCheckWHNF sc trm
         case f trm' of
           Just a -> pure a
           Nothing ->
             fail $ "ensureRecognizer: Expected " ++ s ++ ", found: " ++ showTerm trm'

ensureSort :: SharedContext -> Raw.Term -> IO Sort
ensureSort sc tp = ensureRecognizer "Sort" sc asSort tp

ensurePi :: SharedContext -> Raw.Term -> IO (VarName, Raw.Term, Raw.Term)
ensurePi sc tp = ensureRecognizer "Pi" sc asPi tp

ensurePairType :: SharedContext -> Raw.Term -> IO (Raw.Term, Raw.Term)
ensurePairType sc tp = ensureRecognizer "PairType" sc asPairType tp

ensureRecordType :: SharedContext -> Raw.Term -> IO (Map FieldName Raw.Term)
ensureRecordType sc tp = ensureRecognizer "RecordType" sc asRecordType tp

piSort :: Sort -> Sort -> Sort
piSort s1 s2 = if s2 == propSort then propSort else max s1 s2

-- | Check whether the given 'VarName' occurs free in the type of
-- another variable in the context of the given 'Term', and fail if it
-- does.
ensureNotFreeInContext :: VarName -> Term -> IO ()
ensureNotFreeInContext x body =
  when (any (IntSet.member (vnIndex x) . freeVars) (rawCtx body)) $
    fail $ "Variable occurs free in context: " ++ show (vnName x)
