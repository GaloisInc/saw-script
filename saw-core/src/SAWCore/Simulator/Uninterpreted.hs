{-# LANGUAGE OverloadedStrings #-}

{- |
Module      : SAWCore.Simulator.Uninterpreted
Copyright   : Galois, Inc. 2026
License     : BSD3
Maintainer  : saw@galois.com
Stability   : experimental
Portability : non-portable (language extensions)

Preprocessor for uninterpreted higher-order functions.
-}

module SAWCore.Simulator.Uninterpreted
  ( generalizeHigherOrderFunctions
  , isSimpleType
  , isFirstOrderType
  ) where

import Control.Monad (filterM)
import Data.Foldable (foldlM)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Set (Set)
import qualified Data.Set as Set

import SAWCore.Module
  ( Ctor(..)
  , CtorArg(..)
  , CtorArgStruct(..)
  , DataType(..)
  , ResolvedName(..)
  , lookupVarIndexInMap
  , resolvedNameType
  )
import SAWCore.Name (VarName(..), Name(..))
import SAWCore.Recognizer
import SAWCore.Rewriter
import SAWCore.SharedTerm

-- | Given a set of 'VarIndex'es representing constants with
-- higher-order function types, search a term and collect every
-- subterm that is a partial application of one such constant.
-- The partial application should include as many arguments as
-- necessary to make the resulting function first-order.
--
-- For each such partial application in the term, replace it with a
-- fresh free variable that has a first-order function type.
-- Also create a substitution suitable for use with 'scInstantiate'
-- that maps each new variable to the original subterm.
--
-- For example, the SAWCore function @foldl@ has the following type:
--
-- @foldl : (a b : sort 0) -> (n : Nat) -> (b -> a -> b) -> b -> Vec n a -> b@
--
-- Say the term has a subterm with @foldl@ applied to six arguments:
-- @foldl Bool Bool 8 xor False 0x55@.
-- The partial application @foldl Bool Bool 8 xor@ has the minimum
-- number of arguments required to give it a first-order function
-- type: @Bool -> Vec 8 -> Bool@.
--
-- Thus all occurrences of the subterm @foldl Bool Bool 8 xor@ are
-- replaced with a new free variable @u@ of type @Bool -> Vec 8 Bool
-- -> Bool@.
--
-- The final result will be a term containing @u False 0x55@, and
-- a substitution mapping @u@ to @foldl Bool Bool 8 xor@.
--
-- The preprocessed term should now be suitable for use with a
-- symbolic evaluation backend that supports uninterpreted first-order
-- functions.

generalizeHigherOrderFunctions ::
  SharedContext -> Set VarIndex -> Term -> IO (Term, IntMap Term)
generalizeHigherOrderFunctions sc vs t0 =
  do vs' <- filterCandidates sc vs
     pats <- findFirstOrderApps sc vs' t0
     (ss, sub) <- mkSimpsetSub sc pats
     ((), t1) <- rewriteSharedTerm sc ss t0
     pure (t1, sub)

-- | Given a set of SAWCore constants identified by 'VarIndex', filter
-- them and return the set of constants with higher-order function
-- types.
filterCandidates :: SharedContext -> Set VarIndex -> IO (Set VarIndex)
filterCandidates sc vs =
  Set.fromList <$> filterM (isHigherOrderVarIndex sc) (Set.toList vs)

-- | Look up the type of a SAWCore constant by the 'VarIndex' of its
-- name, and return 'True' if it has a higher-order function type.
isHigherOrderVarIndex :: SharedContext -> VarIndex -> IO Bool
isHigherOrderVarIndex sc i =
  do mm <- scGetModuleMap sc
     case lookupVarIndexInMap i mm of
       Just r -> not <$> isFirstOrderType sc (resolvedNameType r)
       Nothing -> pure False

-- | Given a list of 'Term' patterns, invent a variable for each.
-- Build a 'Simpset' to turn the patterns into the corresponding
-- variables and a substitution to convert them back.
mkSimpsetSub :: SharedContext -> [Term] -> IO (Simpset a, IntMap Term)
mkSimpsetSub _ [] = pure (emptySimpset, IntMap.empty)
mkSimpsetSub sc (t : ts) =
  do (ss, sub) <- mkSimpsetSub sc ts
     vn <- scFreshVarName sc "u"
     let vars = getAllVars t
     ty <- scTypeOf sc t
     ty' <- scPiList sc vars ty
     v <- scVariable sc vn ty'
     rhs <- scApplyAll sc v =<< scVariables sc vars
     eq <- scGlobalApply sc "Prelude.Eq" [ty, t, rhs]
     prop <- scPiList sc vars eq
     let rule = ruleOfTerm prop Nothing
     let ss' = addRule rule ss
     f <- scLambdaList sc vars t
     let sub' = IntMap.insert (vnIndex vn) f sub
     pure (ss', sub')

-- | Given a set of 'VarIndex'es representing constants with
-- higher-order function types, search a term and collect every
-- subterm that is a partial application of one such constant.
-- The partial application should include as many arguments as
-- necessary to make the resulting function first-order.
--
-- For example, the SAWCore function @foldl@ has the following type:
--
-- @foldl : (a b : sort 0) -> (n : Nat) -> (b -> a -> b) -> b -> Vec n a -> b@
--
-- Say the term has a subterm with @foldl@ applied to six arguments:
-- @foldl Bool Bool 8 xor False 0x55@.
-- The final two arguments, @False@ and @0x55@, have simple non-function
-- types, so they can be skipped over.
-- However, the @xor@ argument has a function type, so the partial
-- application must include it.
-- Thus the result list will include @foldl Bool Bool 8 xor@, which
-- has the first-order function type @Bool -> Vec 8 Bool -> Bool@.
findFirstOrderApps :: SharedContext -> Set VarIndex -> Term -> IO [Term]
findFirstOrderApps sc vs t0 = snd <$> go (IntSet.empty, []) t0
  where
    -- foldlM :: (Foldable t, Monad m) => (b -> a -> m b) -> b -> t a -> m b
    go :: (IntSet, [Term]) -> Term -> IO (IntSet, [Term])
    go acc@(seen, ts) t
      | IntSet.member (termIndex t) seen = pure acc
      | otherwise =
          let seen' = IntSet.insert (termIndex t) seen in
          -- Is this term a designated higher-order function applied to arguments?
          case asConstant (fst (asApplyAll t)) of
            Just nm
              | Set.member (nameIndex nm) vs ->
                  -- If so, check whether the outermost argument has a
                  -- simple type.
                  case asApp t of
                    Nothing -> pure (seen', ts)
                    Just (_t1, t2) ->
                      do ty2 <- scTypeOf sc t2
                         simple <- isSimpleType sc ty2
                         case simple of
                           -- If it's simple, then we don't need to
                           -- record a pattern; recurse.
                           True -> foldlM go (seen', ts) (unwrapTermF t)
                           -- If it's *not* simple, then record a
                           -- pattern.
                           False -> pure (seen', t : ts)
            _ -> foldlM go (seen', ts) (unwrapTermF t)


-- | Return true for any function type where all the argument types
-- and the result type are simple types; return false otherwise.
isFirstOrderType :: SharedContext -> Term -> IO Bool
isFirstOrderType sc t =
  do t' <- scWhnf sc t
     case asPi t' of
       Just (_, a, b) ->
         do ok <- isSimpleType sc a
            if ok then isFirstOrderType sc b else pure False
       Nothing ->
         isSimpleType sc t'

-- | Return false for any type containing a function type.
-- Return true for primitive base types, pairs or vectors of simple
-- types, and non-recursive datatypes with only simple constructor
-- argument types.
-- Precondition: The type of the term argument should be a sort.
isSimpleType :: SharedContext -> Term -> IO Bool
isSimpleType sc t =
  do t' <- scWhnf sc t
     case t' of
       -- We consider type variables to be simple, optimistically
       -- assuming that they will be instantiated with simple types.
       (asVariable -> Just _) -> pure True
       -- Pi types are not simple.
       (asPi -> Just _) -> pure False
       -- Sorts are simple.
       (asSort -> Just _) -> pure True
       -- Primitive base types are simple.
       (asGlobalDef -> Just "Prelude.String") -> pure True
       (asGlobalDef -> Just "Prelude.Float") -> pure True
       (asGlobalDef -> Just "Prelude.Double") -> pure True
       (asRationalType -> Just ()) -> pure True
       (asIntegerType -> Just ()) -> pure True
       (asIntModType -> Just _) -> pure True
       -- Booleans and naturals are simple.
       (asBoolType -> Just ()) -> pure True
       (asNatType -> Just ()) -> pure True
       -- Vectors and pairs are simple if their arguments are.
       (asVectorType -> Just (_n, a)) -> isSimpleType sc a
       (asPairType -> Just (a, b)) ->
         allM (isSimpleType sc) [a, b]
       -- Nonrecursive datatypes are simple if all their constructor
       -- argument types are.
       (asApplyAll -> (asConstant -> Just nm, args)) ->
         do mm <- scGetModuleMap sc
            -- look up name; if it's a datatype, then check all its arguments
            case lookupVarIndexInMap (nameIndex nm) mm of
              Just (ResolvedDataType dt) ->
                do let sub = IntMap.fromList (zip (map (vnIndex . fst) (dtParams dt)) args)
                   allM (checkCtorArgStruct sub . ctorArgStruct) (dtCtors dt)
              _ -> pure False
       -- No other cases are considered simple.
       _ -> pure False
  where
    checkCtorArgStruct :: IntMap Term -> CtorArgStruct -> IO Bool
    checkCtorArgStruct sub cas =
      allM (checkCtorArg sub . snd) (ctorArgs cas)

    checkCtorArg :: IntMap Term -> CtorArg -> IO Bool
    checkCtorArg sub carg =
      case carg of
        ConstArg ty -> isSimpleType sc =<< scInstantiate sc sub ty
        RecursiveArg{} -> pure False


allM :: (Monad m) => (a -> m Bool) -> [a] -> m Bool
allM _ [] = pure True
allM f (x : xs) =
  do b <- f x
     if b then allM f xs else pure False
