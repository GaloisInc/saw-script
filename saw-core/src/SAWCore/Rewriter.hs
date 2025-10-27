{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

{- |
Module      : SAWCore.Rewriter
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module SAWCore.Rewriter
  ( -- * Rewrite rules
    RewriteRule
  , ctxtRewriteRule
  , lhsRewriteRule
  , rhsRewriteRule
  , annRewriteRule
  , ruleOfTerm
  , ruleOfTerms
  , ruleOfProp
  , propOfRewriteRule
  , scDefRewriteRules
  , scEqsRewriteRules
  , scEqRewriteRule
    -- * Simplification sets
  , Simpset
  , emptySimpset
  , addRule
  , delRule
  , addRules
  , addSimp
  , delSimp
  , addConv
  , addConvs
  , scSimpset
  , listRules
  , shallowRule
  -- * Term rewriting
  , rewriteSharedTerm
  , rewriteSharedTermTypeSafe
  -- * Matching
  , scMatch
  -- * Miscellaneous
  , replaceTerm
  , hoistIfs
  ) where

import Control.Monad (MonadPlus(..), (>=>), guard)
import Control.Monad.Trans.Class (MonadTrans(..))
import Control.Monad.Trans.Maybe
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.IORef
import qualified Data.Foldable as Foldable
import qualified Data.List as List
import Data.List.Extra (nubOrd)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad.Trans.Writer.Strict
import Numeric.Natural

import qualified SAWSupport.Pretty as PPS (defaultOpts)

import SAWCore.Cache
import SAWCore.Conversion
import SAWCore.Module
  ( ctorName
  , ctorNumParams
  , lookupVarIndexInMap
  , Ctor(..)
  , DataType(..)
  , Def(..)
  , ResolvedName(..)
  )
import SAWCore.Name
import SAWCore.Panic (panic)
import qualified SAWCore.Recognizer as R
import SAWCore.SharedTerm
import SAWCore.Term.Functor
import SAWCore.Term.Pretty (scPrettyTerm)
import SAWCore.Term.Raw
import qualified SAWCore.TermNet as Net
import SAWCore.Prelude.Constants

data RewriteRule a
  = RewriteRule
    { ctxt :: [(VarName, Term)]
    , lhs :: Term
    , rhs :: Term
    , permutative :: Bool
    , shallow :: Bool
    , annotation :: Maybe a
    }
  deriving (Show)
-- ^ Invariant: The set of loose variables in @lhs@ must be exactly
-- @[0 .. length ctxt - 1]@. The @rhs@ may contain a subset of these.

-- NB, exclude the annotation from equality tests
instance Eq (RewriteRule a) where
  RewriteRule c1 l1 r1 p1 s1 _a1 == RewriteRule c2 l2 r2 p2 s2 _a2 =
    c1 == c2 && l1 == l2 && r1 == r2 && p1 == p2 && s1 == s2

ctxtRewriteRule :: RewriteRule a -> [(VarName, Term)]
ctxtRewriteRule = ctxt

lhsRewriteRule :: RewriteRule a -> Term
lhsRewriteRule = lhs

rhsRewriteRule :: RewriteRule a -> Term
rhsRewriteRule = rhs

annRewriteRule :: RewriteRule a -> Maybe a
annRewriteRule = annotation

-- | Convert a rewrite rule to a proposition (a 'Term' of SAWCore type
-- @Prop@) representing the meaning of the rewrite rule.
propOfRewriteRule :: SharedContext -> RewriteRule a -> IO Term
propOfRewriteRule sc rule =
  do ty <- scTypeOf sc (lhs rule)
     eq <- scGlobalApply sc "Prelude.Eq" [ty, lhs rule, rhs rule]
     scPiList sc (ctxt rule) eq

----------------------------------------------------------------------
-- Matching

data MatchState =
  MatchState
  { substitution :: IntMap Term
    -- ^ Mapping of variables, indexed by 'VarIndex'
  , constraints :: [(Term, Natural)]
  }

emptyMatchState :: MatchState
emptyMatchState = MatchState { substitution = IntMap.empty, constraints = [] }


-- First-order matching

-- | Equivalent to @(lookup k t, insert k x t)@.
insertLookup :: VarIndex -> a -> IntMap a -> (Maybe a, IntMap a)
insertLookup k x t = IntMap.insertLookupWithKey (\_ a _ -> a) k x t

firstOrderMatch :: [(VarName, Term)] -> Term -> Term -> Maybe (IntMap Term)
firstOrderMatch ctxt pat term = match pat term IntMap.empty
  where
    ixs :: IntSet
    ixs = IntSet.fromList (map (vnIndex . fst) ctxt)
    match :: Term -> Term -> IntMap Term -> Maybe (IntMap Term)
    match x y m =
      case (unwrapTermF x, unwrapTermF y) of
        (Variable (vnIndex -> i) _, _) | IntSet.member i ixs ->
            case my' of
              Nothing -> Just m'
              Just y' -> if alphaEquiv y y' then Just m' else Nothing
            where (my', m') = insertLookup i y m
        (App x1 x2, App y1 y2) ->
            match x1 y1 m >>= match x2 y2
        (FTermF xf, FTermF yf) ->
            do zf <- zipWithFlatTermF match xf yf
               Foldable.foldl (>=>) Just zf m
        (_, _) ->
            if alphaEquiv x y then Just m else Nothing
-- ^ Precondition: Every loose variable in the pattern @pat@ must
-- occur as the 2nd argument of an @App@ constructor. This ensures
-- that instantiations are well-typed.

-- | Test if a term is a constant natural number
asConstantNat :: Term -> Maybe Natural
asConstantNat t =
  case t of
    (R.asGlobalApply preludeZeroIdent -> Just []) -> Just 0
    (R.asGlobalApply preludeSuccIdent -> Just [x]) -> (+ 1) <$> asConstantNat x
    _ ->
      do let (f, xs) = R.asApplyAll t
         i <- R.asGlobalDef f
         case xs of
           [x, y]
             | i == "Prelude.addNat" -> (+) <$> asConstantNat x <*> asConstantNat y
             | i == "Prelude.mulNat" -> (*) <$> asConstantNat x <*> asConstantNat y
             | i == "Prelude.expNat" -> (^) <$> asConstantNat x <*> asConstantNat y
             | i == "Prelude.subNat" ->
                 do x' <- asConstantNat x
                    y' <- asConstantNat y
                    guard (x' >= y')
                    return (x' - y')
             | i == "Prelude.divNat" ->
                 do x' <- asConstantNat x
                    y' <- asConstantNat y
                    guard (y' > 0)
                    return (x' `div` y')
             | i == "Prelude.remNat" ->
                 do x' <- asConstantNat x
                    y' <- asConstantNat y
                    guard (y' > 0)
                    return (x' `rem` y')
           _ -> Nothing

-- | An enhanced matcher that can handle higher-order patterns.
--
--   This matching procedure will attempt to find an instantiation
--   for the dangling variables appearing in @pattern@.
--   The resulting instantation will return terms that are in the same
--   variable-scoping context as @term@.  In particular, if @term@
--   is closed, then the terms in the instantiation will also be closed.
scMatch ::
  SharedContext ->
  [(VarName, Term)] {- ^ context of unification variables in pattern -} ->
  Term {- ^ pattern -} ->
  Term {- ^ term -} ->
  IO (Maybe (IntMap Term))
scMatch sc ctxt pat term =
  runMaybeT $
  do -- lift $ putStrLn $ "********** scMatch **********"
     MatchState inst cs <- match IntSet.empty pat term emptyMatchState
     mapM_ (check inst) cs
     return inst
  where
    -- The set of VarIndexes of the unification variables
    ixs :: IntSet
    ixs = IntSet.fromList (map (vnIndex . fst) ctxt)
    -- Check that a constraint of the form pat = n for natural number literal n
    -- is satisfied by the supplied substitution (aka instantiation) inst
    check :: IntMap Term -> (Term, Natural) -> MaybeT IO ()
    check inst (t, n) = do
      --lift $ putStrLn $ "checking: " ++ show (t, n)
      -- apply substitution to the term
      t' <- lift $ scInstantiate sc inst t
      --lift $ putStrLn $ "t': " ++ show t'
      -- constant-fold nat operations
      -- ensure that it evaluates to the same number
      case asConstantNat t' of
        Just i | i == n -> return ()
        _ -> mzero

    -- Check if a term is a higher-order variable pattern, i.e., a free variable
    -- (meaning one that can match anything) applied to 0 or more bound variable
    -- arguments.
    asVarPat :: IntSet -> Term -> Maybe (VarIndex, [(VarName, Term)])
    asVarPat locals = go []
      where
        go js x =
          case unwrapTermF x of
            Variable nm _tp
              | IntSet.member (vnIndex nm) ixs -> Just (vnIndex nm, js)
              | otherwise  -> Nothing
            App t (unwrapTermF -> Variable nm tp)
              | IntSet.member (vnIndex nm) locals -> go ((nm, tp) : js) t
            _ -> Nothing

    -- Test if term y matches pattern x, meaning whether there is a substitution
    -- to the free variables of x to make it equal to y.
    -- The IntSet contains the VarIndexes named variables that are locally bound.
    match :: IntSet -> Term -> Term -> MatchState -> MaybeT IO MatchState
    match _ t@(STApp{stAppIndex = i}) (STApp{stAppIndex = j}) s
      | closedTerm t && i == j = return s
    match locals x y s@(MatchState m cs) =
      -- (lift $ putStrLn $ "matching (lhs): " ++ scPrettyTerm PPS.defaultOpts x) >>
      -- (lift $ putStrLn $ "matching (rhs): " ++ scPrettyTerm PPS.defaultOpts y) >>
      case asVarPat locals x of
        -- If the lhs pattern is of the form (?u b1..bk) where ?u is a
        -- unification variable and b1..bk are all locally bound
        -- variables: First check whether the rhs contains any locally
        -- bound variables *not* in the list b1..bk. If it contains any
        -- others, then there is no match. If it only uses a subset of
        -- b1..bk, then we can instantiate ?u to (\b1..bk -> rhs).
        Just (i, vs) ->
          do -- ensure parameter variables are distinct
             guard (Set.size (Set.fromList vs) == length vs)
             -- ensure y mentions only variables that are in vs
             let vset = IntSet.fromList (map (vnIndex . fst) vs)
             guard (IntSet.disjoint (IntSet.difference locals vset) (freeVars y))
             y2 <- lift $ scLambdaList sc vs y
             let (my3, m') = insertLookup i y2 m
             case my3 of
               Nothing -> return (MatchState m' cs)
               Just y3 -> if y2 == y3 then return (MatchState m' cs) else mzero
        Nothing ->
          case (unwrapTermF x, unwrapTermF y) of
            (_, FTermF (NatLit n))
              | Just [x'] <- R.asGlobalApply preludeSuccIdent x
              , n > 0 ->
                do y' <- lift $ scNat sc (n-1)
                   match locals x' y' s
            -- check that neither x nor y contains bound variables less than `depth`
            (FTermF xf, FTermF yf) ->
              case zipWithFlatTermF (match locals) xf yf of
                Nothing -> mzero
                Just zf -> Foldable.foldl (>=>) return zf s
            (App x1 x2, App y1 y2) ->
              match locals x1 y1 s >>= match locals x2 y2
            (Lambda nm t1 x1, Lambda _ t2 x2) ->
              match locals t1 t2 s >>= match (IntSet.insert (vnIndex nm) locals) x1 x2
            (Pi nm t1 x1, Pi _ t2 x2) ->
              match locals t1 t2 s >>= match (IntSet.insert (vnIndex nm) locals) x1 x2
            (App _ _, FTermF (NatLit n)) ->
              -- add deferred constraint
              return (MatchState m ((x, n) : cs))
            (_, _) ->
              -- other possible matches are local vars and constants
              if x == y then return s else mzero

----------------------------------------------------------------------
-- Building rewrite rules

eqIdent :: Ident
eqIdent = mkIdent (mkModuleName ["Prelude"]) "Eq"

ecEqIdent :: Ident
ecEqIdent = mkIdent (mkModuleName ["Cryptol"]) "ecEq"

bvEqIdent :: Ident
bvEqIdent = mkIdent (mkModuleName ["Prelude"]) "bvEq"

boolEqIdent :: Ident
boolEqIdent = mkIdent (mkModuleName ["Prelude"]) "boolEq"

vecEqIdent :: Ident
vecEqIdent = mkIdent (mkModuleName ["Prelude"]) "vecEq"

pairEqIdent :: Ident
pairEqIdent = mkIdent (mkModuleName ["Prelude"]) "pairEq"

arrayEqIdent :: Ident
arrayEqIdent = mkIdent (mkModuleName ["Prelude"]) "arrayEq"

equalNatIdent :: Ident
equalNatIdent = mkIdent (mkModuleName ["Prelude"]) "equalNat"

intEqIdent :: Ident
intEqIdent = mkIdent (mkModuleName ["Prelude"]) "intEq"

intModEqIdent :: Ident
intModEqIdent = mkIdent (mkModuleName ["Prelude"]) "intModEq"

-- | Converts a universally quantified equality proposition from a
-- Term representation to a RewriteRule.
ruleOfTerm :: Term -> Maybe a -> RewriteRule a
ruleOfTerm t ann =
  do let (vars, body) = R.asPiList t
     case R.asGlobalApply eqIdent body of
       Just [_, x, y] -> mkRewriteRule vars x y False ann
       _ -> panic "ruleOfTerm" ["Illegal argument"]

-- Test whether a rewrite rule is permutative
-- this is a rule that immediately loops whether used forwards or backwards.
rulePermutes :: [(VarName, Term)] -> Term -> Term -> Bool
rulePermutes ctxt lhs rhs =
    case firstOrderMatch ctxt lhs rhs of
        Nothing -> False -- rhs is not an instance of lhs
        Just _ ->
          case firstOrderMatch ctxt rhs lhs of
            Nothing -> False -- but here we have a looping rule, not good!
            Just _ -> True

mkRewriteRule :: [(VarName, Term)] -> Term -> Term -> Bool -> Maybe a -> RewriteRule a
mkRewriteRule c l r shallow ann =
    RewriteRule
    { ctxt = c
    , lhs = l
    , rhs = r
    , permutative = rulePermutes c l r
    , shallow = shallow
    , annotation = ann
    }

-- | Converts a universally quantified equality proposition between the
-- two given terms to a RewriteRule.
ruleOfTerms :: Term -> Term -> RewriteRule a
ruleOfTerms l r = mkRewriteRule [] l r False Nothing

-- | Converts a parameterized equality predicate to a RewriteRule,
-- returning 'Nothing' if the predicate is not an equation.
ruleOfProp :: SharedContext -> Term -> Maybe a -> IO (Maybe (RewriteRule a))
ruleOfProp sc term ann =
  case R.asPi term of
  Just (nm, tp, body) ->
    do rule <- ruleOfProp sc body ann
       pure $ (\r -> r { ctxt = (nm, tp) : ctxt r}) <$> rule
  Nothing ->
    case R.asLambda term of
    Just (nm, tp, body) ->
      do rule <- ruleOfProp sc body ann
         pure $ (\r -> r { ctxt = (nm, tp) : ctxt r}) <$> rule
    Nothing ->
      case term of
        (R.asGlobalApply ecEqIdent -> Just [_, _, x, y]) -> eqRule x y
        (R.asGlobalApply bvEqIdent -> Just [_, x, y]) -> eqRule x y
        (R.asGlobalApply equalNatIdent -> Just [x, y]) -> eqRule x y
        (R.asGlobalApply boolEqIdent -> Just [x, y]) -> eqRule x y
        (R.asGlobalApply vecEqIdent -> Just [_, _, _, x, y]) -> eqRule x y
        (R.asGlobalApply pairEqIdent -> Just [_, _, _, _, x, y]) -> eqRule x y
        (R.asGlobalApply arrayEqIdent -> Just [_, _, x, y]) -> eqRule x y
        (R.asGlobalApply intEqIdent -> Just [x, y]) -> eqRule x y
        (R.asGlobalApply intModEqIdent -> Just [_, x, y]) -> eqRule x y
        (unwrapTermF -> Constant nm) ->
          do mres <- lookupVarIndexInMap (nameIndex nm) <$> scGetModuleMap sc
             case mres of
               Just (ResolvedDef (defBody -> Just body)) -> ruleOfProp sc body ann
               _ -> pure Nothing
        (R.asEq -> Just (_, x, y)) -> eqRule x y
        (R.asEqTrue -> Just body) -> ruleOfProp sc body ann
        (R.asApplyAll -> (R.asConstant -> Just nm, args)) ->
          do mres <- lookupVarIndexInMap (nameIndex nm) <$> scGetModuleMap sc
             case mres of
               Just (ResolvedDef (defBody -> Just body)) ->
                 do app <- scApplyAllBeta sc body args
                    ruleOfProp sc app ann
               _ -> pure Nothing
        _ -> pure Nothing

  where
    eqRule x y = pure $ Just $ mkRewriteRule [] x y False ann

-- | Generate a rewrite rule from the type of an identifier, using 'ruleOfTerm'
scEqRewriteRule :: SharedContext -> Ident -> IO (RewriteRule a)
scEqRewriteRule sc i = ruleOfTerm <$> scTypeOfIdent sc i <*> pure Nothing

-- | Collects rewrite rules from named constants, whose types must be equations.
scEqsRewriteRules :: SharedContext -> [Ident] -> IO [RewriteRule a]
scEqsRewriteRules sc = mapM (scEqRewriteRule sc)

-- | Transform the given rewrite rule to a set of one or more
-- equivalent rewrite rules, if possible.
--
-- * If the rhs is a lambda, then add an argument to the lhs.
-- * If the rhs is a recursor, then split into a separate rule for each constructor.
-- * If the rhs is a record, then split into a separate rule for each accessor.
scExpandRewriteRule :: SharedContext -> RewriteRule a -> IO (Maybe [RewriteRule a])
scExpandRewriteRule sc (RewriteRule ctxt lhs rhs _ shallow ann) =
  case R.asLambda rhs of
  Just (nm, tp, body) ->
    do let ctxt' = ctxt ++ [(nm, tp)]
       var0 <- scVariable sc nm tp
       lhs' <- scApply sc lhs var0
       pure $ Just [mkRewriteRule ctxt' lhs' body shallow ann]
  Nothing ->
    case rhs of
    (R.asRecordValue -> Just m) ->
      do let mkRule (k, x) =
               do l <- scRecordSelect sc lhs k
                  return (mkRewriteRule ctxt l x shallow ann)
         Just <$> traverse mkRule (Map.assocs m)
    (R.asApplyAll ->
     (R.asRecursorApp -> Just (r, crec),
      splitAt (recursorNumParams crec) ->
      (params,
       motive :
       (splitAt (length (recursorCtorOrder crec)) ->
        (elims,
         splitAt (recursorNumIxs crec) ->
         (_ixs, (R.asVariable -> Just (x, xt)) : more))))))
      | (ctxt1, _ : ctxt2) <- break ((== x) . fst) ctxt ->
      do -- ti is the type of the value being scrutinized
         ti <- scWhnf sc xt
         -- The datatype parameters are also in context @ctxt1@.
         let (_d, (params1, _ixs)) = fmap (splitAt (recursorNumParams crec)) (R.asApplyAll ti)
         let ctorRule ctor =
               do -- Compute the argument types @argTs@.
                  ctorT <- piAppType (ctorType ctor) params1
                  argCtx <- fst <$> asFreshPiList sc ctorT
                  -- Build a fully-applied constructor @c@.
                  args <- scVariables sc argCtx
                  c <- scConstApply sc (ctorName ctor) (params1 ++ args)
                  -- Define function to substitute the constructor @c@
                  -- in for the old local variable @x@.
                  let subst = IntMap.singleton (vnIndex x) c
                  let adjust t = scInstantiate sc subst t
                  -- Build the list of types of the new context.
                  ctxt2' <- traverse (traverse adjust) ctxt2
                  let ctxt' = ctxt1 ++ argCtx ++ ctxt2'
                  -- Substitute the new constructor value to make the
                  -- new lhs and rhs in context @ctxt'@.
                  lhs' <- adjust lhs

                  r'  <- adjust r
                  more' <- traverse adjust more

                  rhs1 <- scReduceRecursor sc r' crec params motive elims (ctorName ctor) args
                  rhs2 <- scApplyAll sc rhs1 more'
                  rhs3 <- betaReduce rhs2
                  -- re-fold recursive occurrences of the original rhs
                  let ss = addRule (mkRewriteRule ctxt rhs lhs shallow Nothing) emptySimpset
                  (_,rhs') <- rewriteSharedTerm sc (ss :: Simpset ()) rhs3
                  return (mkRewriteRule ctxt' lhs' rhs' shallow ann)
         let d = recursorDataType crec
         mm <- scGetModuleMap sc
         dt <-
           case lookupVarIndexInMap (nameIndex d) mm of
             Just (ResolvedDataType dt) -> pure dt
             _ -> panic "scExpandRewriteRule" ["Datatype not found: " <> toAbsoluteName (nameInfo d)]
         rules <- traverse ctorRule (dtCtors dt)
         return (Just rules)
    _ -> return Nothing
  where
    piAppType :: Term -> [Term] -> IO Term
    piAppType funtype [] = return funtype
    piAppType funtype (arg : args) =
      do funtype' <- reducePi sc funtype arg
         piAppType funtype' args

    betaReduce :: Term -> IO Term
    betaReduce t =
      case R.asApp t of
        Nothing -> return t
        Just (f, arg) ->
          do f' <- betaReduce f
             case R.asLambda f' of
               Nothing -> scApply sc f' arg
               Just (vn, _, body) ->
                 scInstantiate sc (IntMap.singleton (vnIndex vn) arg) body

-- | Like 'R.asPiList', but freshen all variables in the context.
asFreshPiList :: SharedContext -> Term -> IO ([(VarName, Term)], Term)
asFreshPiList sc t =
  case R.asPi t of
    Nothing -> pure ([], t)
    Just (x, t1, t2) ->
      do -- never use "_" as the base name
         let basename = if vnName x == "_" then "_x" else vnName x
         x' <- scFreshVarName sc basename
         var <- scVariable sc x' t1
         t2' <- scInstantiate sc (IntMap.singleton (vnIndex x) var) t2
         (ctx, body) <- asFreshPiList sc t2'
         pure ((x', t1) : ctx, body)

-- | Repeatedly apply the rule transformations in 'scExpandRewriteRule'.
scExpandRewriteRules :: SharedContext -> [RewriteRule a] -> IO [RewriteRule a]
scExpandRewriteRules sc rs =
  case rs of
    [] -> return []
    r : rs2 ->
      do m <- scExpandRewriteRule sc r
         case m of
           Nothing -> (r :) <$> scExpandRewriteRules sc rs2
           Just rs1 -> scExpandRewriteRules sc (rs1 ++ rs2)

-- | Create a rewrite rule for a definition that expands the definition, if it
-- has a body to expand to, otherwise return the empty list
scDefRewriteRules :: SharedContext -> Def -> IO [RewriteRule a]
scDefRewriteRules sc d =
  case defBody d of
    Just rhs ->
      do lhs <- scConst sc (defName d)
         scExpandRewriteRules sc [mkRewriteRule [] lhs rhs False Nothing]
    Nothing ->
      pure []

-- | A "shallow" rule is one where further
--   rewrites are not applied to the result
--   of a rewrite.
shallowRule :: RewriteRule a -> RewriteRule a
shallowRule r = r{ shallow = True }

----------------------------------------------------------------------
-- Simpsets

-- | Invariant: 'Simpset's should not contain reflexive rules. We avoid
-- adding them in 'addRule' below.
type Simpset a = Net.Net (Either (RewriteRule a) Conversion)

emptySimpset :: Simpset a
emptySimpset = Net.empty

addRule :: RewriteRule a -> Simpset a -> Simpset a
addRule rule | lhs rule /= rhs rule = Net.insert_term (termPat (lhs rule), Left rule)
             | otherwise = id

delRule :: RewriteRule a -> Simpset a -> Simpset a
delRule rule = Net.delete_term (termPat (lhs rule), Left rule)

addRules :: [RewriteRule a] -> Simpset a -> Simpset a
addRules rules ss = foldr addRule ss rules

addSimp :: Term -> Maybe a -> Simpset a -> Simpset a
addSimp prop ann = addRule (ruleOfTerm prop ann)

delSimp :: Term -> Simpset a -> Simpset a
delSimp prop = delRule (ruleOfTerm prop Nothing)

addConv :: Conversion -> Simpset a -> Simpset a
addConv conv = Net.insert_term (conversionPat conv, Right conv)

addConvs :: [Conversion] -> Simpset a -> Simpset a
addConvs convs ss = foldr addConv ss convs

scSimpset :: SharedContext -> [Def] -> [Ident] -> [Conversion] -> IO (Simpset a)
scSimpset sc defs eqIdents convs = do
  defRules <- concat <$> traverse (scDefRewriteRules sc) defs
  eqRules <- mapM (scEqRewriteRule sc) eqIdents
  return $ addRules defRules $ addRules eqRules $ addConvs convs $ emptySimpset

listRules :: Simpset a -> [RewriteRule a]
listRules ss = [ r | Left r <- Net.content ss ]

----------------------------------------------------------------------
-- Destructors for terms

asBetaRedex :: R.Recognizer Term (VarName, Term, Term, Term)
asBetaRedex t =
    do (f, arg) <- R.asApp t
       (s, ty, body) <- R.asLambda f
       return (s, ty, body, arg)

asPairRedex :: R.Recognizer Term Term
asPairRedex t =
    do (u, b) <- R.asPairSelector t
       (x, y) <- R.asPairValue u
       return (if b then y else x)

asRecordRedex :: R.Recognizer Term Term
asRecordRedex t =
    do (x, i) <- R.asRecordSelector t
       ts <- R.asRecordValue x
       case Map.lookup i ts of
         Just t' -> return t'
         Nothing -> fail "Record field not found"

-- | An iota redex whose argument is a concrete nautral number; specifically,
--   this function recognizes
--
--   > RecursorApp rec _ n
asNatIotaRedex :: R.Recognizer Term (Term, Term, Natural)
asNatIotaRedex t =
  do (r_m_f1_f2, arg) <- R.asApp t
     (r_m_f1, f2) <- R.asApp r_m_f1_f2
     (r_m, f1) <- R.asApp r_m_f1
     (r, _m) <- R.asApp r_m
     _ <- R.asRecursorApp r
     n <- R.asNat arg
     Just (f1, f2, n)

----------------------------------------------------------------------
-- Bottom-up rewriting

-- | Term ordering
-- The existing "<" on terms is not adequate for deciding how to handle permutative rules,
-- as then associativity and commutativity can loop.
-- The following rather unsophisticated functions *might* prevent looping.
-- More analysis is needed!
--
-- here we get the "fringe" of arguments in an application, looking at either curried or
-- tupled arguments.  That is
--   for `f x y z`, return [x,y,z]
--   for `f (x,y)` return [x,y]
--   for `f (f x y) z`, return [x,y,z]
--   for `f (x, f (y,z))`, return [x,y,z]
appCollectedArgs :: Term -> [Term]
appCollectedArgs t = step0 t []
  where
    -- step 0: accumulate curried args, find the function
    step0 :: Term -> [Term] -> [Term]
    step0 (R.asApp -> Just (f, a)) args = step0 f (a : args)
    step0 other args = step1 other args
    -- step 1: analyse each arg, knowing the called function, append together
    step1 :: Term -> [Term] -> [Term]
    step1 f args = foldl (++) [] (map (step2 f) args)
    -- step2: analyse an arg.  look inside tuples, sequences (TBD), more calls to f
    step2 :: Term -> Term -> [Term]
    step2 f (R.asPairValue -> Just (x, y)) = step2 f x ++ step2 f y
    step2 f (s@(R.asApp -> Just (g, a))) = possibly_curried_args s f g (step2 f a)
    step2 _ a = [a]
    --
    possibly_curried_args :: Term -> Term -> Term -> [Term] -> [Term]
    possibly_curried_args s f (R.asApp -> Just (g, a)) args =
      possibly_curried_args s f g (step2 f a ++ args)
    possibly_curried_args s f h args = if f == h then args else [s]


termWeightLt :: Term -> Term -> Bool
termWeightLt t t' =
  (appCollectedArgs t) < (appCollectedArgs t')

-- | Do a single reduction step (beta, record or tuple selector) at top
-- level, if possible.
reduceSharedTerm :: SharedContext -> Term -> IO (Maybe Term)
reduceSharedTerm sc (asBetaRedex -> Just (vn, _, body, arg)) =
  Just <$> scInstantiate sc (IntMap.singleton (vnIndex vn) arg) body
reduceSharedTerm _ (asPairRedex -> Just t) = pure (Just t)
reduceSharedTerm _ (asRecordRedex -> Just t) = pure (Just t)
reduceSharedTerm sc (asNatIotaRedex -> Just (f1, f2, n)) =
  Just <$> scReduceNatRecursor sc f1 f2 n
reduceSharedTerm sc
  (R.asApp -> Just (R.asApplyAll -> (R.asRecursorApp -> Just (r, crec),
                                     splitAt (recursorNumParams crec) -> (params, motive : elims_ixs)), arg))
  | length (recursorCtorOrder crec) + recursorNumIxs crec == length elims_ixs =
  do let (f, args) = R.asApplyAll arg
     let elims = take (length (recursorCtorOrder crec)) elims_ixs
     mm <- scGetModuleMap sc
     case R.asConstant f of
       Nothing -> pure Nothing
       Just c ->
         case lookupVarIndexInMap (nameIndex c) mm of
           Just (ResolvedCtor ctor) ->
             Just <$> scReduceRecursor sc r crec params motive elims c (drop (ctorNumParams ctor) args)
           _ -> pure Nothing
reduceSharedTerm _ _ = pure Nothing

-- | Rewriter for shared terms.  The annotations of any used rules are collected
--   and returned in the result set.
rewriteSharedTerm :: forall a. Ord a => SharedContext -> Simpset a -> Term -> IO (Set a, Term)
rewriteSharedTerm sc ss t0 =
    do cache <- newCache
       let ?cache = cache
       setRef <- newIORef mempty
       let ?annSet = setRef
       t <- rewriteAll t0
       anns <- readIORef setRef
       pure (anns, t)

  where
    rewriteAll :: (?cache :: Cache IO TermIndex Term, ?annSet :: IORef (Set a)) => Term -> IO Term
    rewriteAll STApp{ stAppIndex = tidx, stAppTermF = tf } =
        useCache ?cache tidx (traverseTF rewriteAll tf >>= scTermF sc >>= rewriteTop)

    traverseTF :: forall b. (b -> IO b) -> TermF b -> IO (TermF b)
    traverseTF _ tf@(Constant {}) = pure tf
    traverseTF f tf = traverse f tf

    rewriteTop :: (?cache :: Cache IO TermIndex Term, ?annSet :: IORef (Set a)) => Term -> IO Term
    rewriteTop t =
      do mt <- reduceSharedTerm sc t
         case mt of
           Nothing -> apply (Net.unify_term ss (termPat t)) t
           Just t' -> rewriteAll t'

    recordAnn :: (?annSet :: IORef (Set a)) => Maybe a -> IO ()
    recordAnn Nothing  = return ()
    recordAnn (Just a) = modifyIORef' ?annSet (Set.insert a)

    apply :: (?cache :: Cache IO TermIndex Term, ?annSet :: IORef (Set a)) =>
             [Either (RewriteRule a) Conversion] -> Term -> IO Term
    apply [] t = return t
    apply (Left (RewriteRule {ctxt, lhs, rhs, permutative, shallow, annotation}) : rules) t = do
      result <- scMatch sc ctxt lhs t
      case result of
        Nothing -> apply rules t
        Just inst
          | lhs == rhs ->
            -- This should never happen because we avoid inserting
            -- reflexive rules into simp sets in the first place.
            do putStrLn $ "rewriteSharedTerm: skipping reflexive rule " ++
                          "(THE IMPOSSIBLE HAPPENED!): " ++ scPrettyTerm PPS.defaultOpts lhs
               apply rules t
          | IntMap.keysSet inst /= IntSet.fromList (map (vnIndex . fst) ctxt) ->
            do putStrLn $ "rewriteSharedTerm: invalid lhs does not contain all variables: "
                 ++ scPrettyTerm PPS.defaultOpts lhs
               apply rules t
          | permutative ->
            do
              t' <- scInstantiate sc inst rhs
              case termWeightLt t' t of
                True -> recordAnn annotation >> rewriteAll t' -- keep the result only if it is "smaller"
                False -> apply rules t
          | shallow ->
            -- do not to further rewriting to the result of a "shallow" rule
            do recordAnn annotation
               scInstantiate sc inst rhs
          | otherwise ->
            do -- putStrLn "REWRITING:"
               -- print lhs
               recordAnn annotation
               rewriteAll =<< scInstantiate sc inst rhs
    apply (Right conv : rules) t =
        do -- putStrLn "REWRITING:"
           -- print (Net.toPat conv)
           case runConversion conv t of
             Nothing -> apply rules t
             Just tb -> rewriteAll =<< runTermBuilder tb (scGlobalDef sc) (scTermF sc)

-- | Type-safe rewriter for shared terms
rewriteSharedTermTypeSafe :: forall a. Ord a =>
  SharedContext -> Simpset a -> Term -> IO (Set a, Term)
rewriteSharedTermTypeSafe sc ss t0 =
    do cache <- newCache
       let ?cache = cache
       annRef <- newIORef mempty
       let ?annSet = annRef
       t <- rewriteAll t0
       anns <- readIORef annRef
       return (anns, t)

  where
    rewriteAll :: (?cache :: Cache IO TermIndex Term, ?annSet :: IORef (Set a)) =>
                  Term -> IO Term
    rewriteAll STApp{ stAppIndex = tidx, stAppTermF = tf } =
        -- putStrLn "Rewriting term:" >> print t >>
        useCache ?cache tidx (rewriteTermF tf >>= scTermF sc >>= rewriteTop)

    rewriteTermF :: (?cache :: Cache IO TermIndex Term, ?annSet :: IORef (Set a)) =>
                    TermF Term -> IO (TermF Term)
    rewriteTermF tf =
        case tf of
          FTermF ftf -> FTermF <$> rewriteFTermF ftf
          App e1 e2 ->
              do t1 <- scTypeOf sc e1
                 case unwrapTermF t1 of
                   -- We only rewrite e2 if type of e1 is not a dependent type.
                   -- This prevents rewriting e2 from changing type of @App e1 e2@.
                   Pi x _ t
                     | IntSet.notMember (vnIndex x) (freeVars t) ->
                         App <$> rewriteAll e1 <*> rewriteAll e2
                   _ -> App <$> rewriteAll e1 <*> pure e2
          Lambda pat t e -> Lambda pat t <$> rewriteAll e
          Constant{}     -> return tf
          Variable{}     -> return tf
          _ -> return tf -- traverse rewriteAll tf

    rewriteFTermF :: (?cache :: Cache IO TermIndex Term, ?annSet :: IORef (Set a)) =>
                     FlatTermF Term -> IO (FlatTermF Term)
    rewriteFTermF ftf =
        case ftf of
          UnitValue        -> return ftf
          UnitType         -> return ftf
          PairValue{}      -> traverse rewriteAll ftf
          PairType{}       -> return ftf -- doesn't matter
          PairLeft{}       -> traverse rewriteAll ftf
          PairRight{}      -> traverse rewriteAll ftf

          -- NOTE: we don't rewrite arguments of constructors, datatypes, or
          -- recursors because of dependent types, as we could potentially cause
          -- a term to become ill-typed
          Recursor{}       -> return ftf

          RecordType{}     -> traverse rewriteAll ftf
          RecordValue{}    -> traverse rewriteAll ftf
          RecordProj{}     -> traverse rewriteAll ftf
          Sort{}           -> return ftf -- doesn't matter
          NatLit{}         -> return ftf -- doesn't matter
          ArrayValue t es  -> ArrayValue t <$> traverse rewriteAll es
          StringLit{}      -> return ftf

    rewriteTop :: (?cache :: Cache IO TermIndex Term, ?annSet :: IORef (Set a)) =>
                  Term -> IO Term
    rewriteTop t = apply (Net.match_term ss (termPat t)) t

    recordAnn :: (?annSet :: IORef (Set a)) => Maybe a -> IO ()
    recordAnn Nothing  = return ()
    recordAnn (Just a) = modifyIORef' ?annSet (Set.insert a)

    apply :: (?cache :: Cache IO TermIndex Term, ?annSet :: IORef (Set a)) =>
             [Either (RewriteRule a) Conversion] ->
             Term -> IO Term
    apply [] t = return t
    apply (Left rule : rules) t =
      case firstOrderMatch (ctxt rule) (lhs rule) t of
        Nothing -> apply rules t
        Just inst ->
          do recordAnn (annotation rule)
             rewriteAll =<< scInstantiate sc inst (rhs rule)
    apply (Right conv : rules) t =
      case runConversion conv t of
        Nothing -> apply rules t
        Just tb -> rewriteAll =<< runTermBuilder tb (scGlobalDef sc) (scTermF sc)


-- FIXME: is there some way to have sensable term replacement in the presence of loose variables
--  and/or under binders?
replaceTerm :: Ord a =>
  SharedContext ->
  Simpset a    {- ^ A simpset of rewrite rules to apply along with the replacement -} ->
  (Term, Term) {- ^ (pat,repl) is a tuple of a pattern term to replace and a replacement term -} ->
  Term         {- ^ the term in which to perform the replacement -} ->
  IO (Set a, Term)
replaceTerm sc ss (pat, repl) t = do
    let rule = ruleOfTerms pat repl
    let ss' = addRule rule ss
    rewriteSharedTerm sc ss' t


-------------------------------------------------------------------------------
-- If/then/else hoisting

-- | Find all instances of Prelude.ite in the given term and hoist them
--   higher.  An if-then-else floats upward until it hits a binder that
--   binds one of its free variables, or until it bubbles to the top of
--   the term.  When multiple if-then-else branches bubble to the same
--   place, they will be nested via a canonical term ordering.  This transformation
--   also does rewrites by basic boolean identities.
hoistIfs :: SharedContext
         -> Term
         -> IO Term
hoistIfs sc t = do
   cache <- newCache

   rules <- map (\rt -> ruleOfTerm rt Nothing) <$> mapM (scTypeOfIdent sc)
              [ "Prelude.ite_true"
              , "Prelude.ite_false"
              , "Prelude.ite_not"
              , "Prelude.ite_nest1"
              , "Prelude.ite_nest2"
              , "Prelude.ite_eq"
              , "Prelude.ite_bit_false_1"
              , "Prelude.ite_bit_true_1"
              , "Prelude.ite_bit"
              , "Prelude.not_not"
              , "Prelude.and_True1"
              , "Prelude.and_False1"
              , "Prelude.and_True2"
              , "Prelude.and_False2"
              , "Prelude.and_idem"
              , "Prelude.or_True1"
              , "Prelude.or_False1"
              , "Prelude.or_True2"
              , "Prelude.or_False2"
              , "Prelude.or_idem"
              , "Prelude.not_or"
              , "Prelude.not_and"
              ]
   let ss :: Simpset () = addRules rules emptySimpset

   (t', conds) <- doHoistIfs sc ss cache . snd =<< rewriteSharedTerm sc ss t

   -- remove duplicate conditions from the list, as muxing in SAW can result in
   -- many copies of the same condition, which cause a performance issue
   splitConds sc ss (nubOrd $ map fst conds) t'


splitConds :: Ord a => SharedContext -> Simpset a -> [Term] -> Term -> IO Term
splitConds sc ss = go
 where
   go [] t = return t
   go (c:cs) t = go cs =<< splitCond sc ss c t

splitCond :: Ord a => SharedContext -> Simpset a -> Term -> Term -> IO Term
splitCond sc ss c t = do
   ty <- scTypeOf sc t
   trueTerm  <- scBool sc True
   falseTerm <- scBool sc False

   (_,then_branch) <- replaceTerm sc ss (c, trueTerm) t
   (_,else_branch) <- replaceTerm sc ss (c, falseTerm) t
   scGlobalApply sc "Prelude.ite" [ty, c, then_branch, else_branch]


type HoistIfs s = (Term, [(Term, Map VarName Term)])


orderTerms :: SharedContext -> [Term] -> IO [Term]
orderTerms _sc xs = return $ List.sort xs

doHoistIfs :: Ord a =>
  SharedContext ->
  Simpset a ->
  Cache IO TermIndex (HoistIfs s) ->
  Term ->
  IO (HoistIfs s)
doHoistIfs sc ss hoistCache = go

 where go :: Term -> IO (HoistIfs s)
       go t@(STApp{ stAppIndex = idx, stAppTermF = tf}) = useCache hoistCache idx $ top t tf

       top :: Term -> TermF Term -> IO (HoistIfs s)
       top t tf =
         case R.asGlobalApply "Prelude.ite" t of
           Just [branch_tp, cond, then_branch, else_branch] ->
             do (then_branch',conds1) <- go then_branch
                (else_branch',conds2) <- go else_branch
                t' <- scGlobalApply sc "Prelude.ite" [branch_tp, cond, then_branch', else_branch']
                let vars = getAllVarsMap cond
                return (t', (cond, vars) : conds1 ++ conds2)
           _ ->
             goF t tf

       goF :: Term -> TermF Term -> IO (HoistIfs s)

       goF t (Constant {}) = return (t, [])
       goF t (Variable {}) = return (t, [])

       goF _ (FTermF ftf) = do
                (ftf', conds) <- runWriterT $ traverse WriterT $ (fmap go ftf)
                t' <- scFlatTermF sc ftf'
                return (t', conds)

       goF _ (App f x) = do
           (f', conds1) <- go f
           (x', conds2) <- go x
           t' <- scApply sc f' x'
           return (t', conds1 ++ conds2)

       goF _ (Lambda nm tp body) = goBinder scLambda nm tp body
       goF _ (Pi nm tp body) = goBinder scPi nm tp body

       goBinder close nm tp body =
          do (body'', conds) <- go body
             let (stuck, float) = List.partition (Map.member nm . snd) conds

             stuck' <- orderTerms sc (map fst stuck)
             body''' <- splitConds sc ss stuck' body''

             t' <- close sc nm tp body'''
             return (t', float)
