{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

{- |
Module      : SAWCore.Rewriter
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : saw@galois.com
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
  (Conversion(..)
  , termPat
  , conversionPat
  , runConversion
  )
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
import qualified SAWCore.OpenTerm as OT
import SAWCore.Panic (panic)
import qualified SAWCore.Recognizer as R
import SAWCore.SharedTerm
import SAWCore.Term.Functor
import qualified SAWCore.TermNet as Net
import SAWCore.Prelude.Constants

data RewriteRule a
  = RewriteRule
    { ctxt :: [(VarName, Term)]
    , lhs :: Term
    , rhs :: Term
    , permutative :: Bool
    , shallow :: Bool
    , convertible :: Bool -- ^ flag is true if the rule's LHS and RHS are convertible in SAWcore type system
    , annotation :: Maybe a
    }
  deriving (Show)
-- ^ Invariant: The set of loose variables in @lhs@ must be exactly
-- @[0 .. length ctxt - 1]@. The @rhs@ may contain a subset of these.

-- NB, exclude the annotation from equality tests
instance Eq (RewriteRule a) where
  RewriteRule c1 l1 r1 p1 s1 co1 _a1 == RewriteRule c2 l2 r2 p2 s2 co2 _a2 =
    c1 == c2 && l1 == l2 && r1 == r2 && p1 == p2 && s1 == s2 && co1 == co2

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
     MatchState inst cs <- match emptyVarCtx emptyVarCtx [] pat term emptyMatchState
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
    asVarPat :: VarCtx -> Term -> Maybe (VarIndex, [Int])
    asVarPat locals = go []
      where
        go js t =
          case unwrapTermF t of
            Variable x _tp
              | IntSet.member (vnIndex x) ixs -> Just (vnIndex x, js)
              | otherwise  -> Nothing
            App t1 (unwrapTermF -> Variable x _) ->
              case lookupVarCtx x locals of
                Just j -> go (j : js) t1
                Nothing -> Nothing
            _ -> Nothing

    -- Test if term y matches pattern x, meaning whether there is a substitution
    -- to the free variables of x to make it equal to y.
    -- The IntMap contains the VarIndexes of locally bound variables.
    -- The first two arguments are the bound variable contexts of x and y, respectively.
    match ::
      VarCtx -> VarCtx -> [(VarName, Term)] ->
      Term -> Term -> MatchState -> MaybeT IO MatchState
    match (VarCtx _ xm) (VarCtx _ ym) _ x y s
      | termIndex x == termIndex y &&
        -- bound variables must also refer to the same de Bruijn indices
        IntMap.intersection xm (varTypes x) ==
        IntMap.intersection ym (varTypes y) = pure s
    match xenv yenv ybinds x y s@(MatchState m cs) =
      -- (lift $ putStrLn $ "matching (lhs): " ++ ppTermPure PPS.defaultOpts x) >>
      -- (lift $ putStrLn $ "matching (rhs): " ++ ppTermPure PPS.defaultOpts y) >>
      case asVarPat xenv x of
        -- If the lhs pattern is of the form (?u b1..bk) where ?u is a
        -- unification variable and b1..bk are all locally bound
        -- variables: First check whether the rhs contains any locally
        -- bound variables *not* in the list b1..bk. If it contains any
        -- others, then there is no match. If it only uses a subset of
        -- b1..bk, then we can instantiate ?u to (\b1..bk -> rhs).
        Just (i, js) ->
          do -- ensure parameter variables are distinct
             guard (Set.size (Set.fromList js) == length js)
             -- ensure y mentions no local variables not in js
             let VarCtx ysize ym = yenv
             let ks = map (ysize -) $ IntMap.elems $ IntMap.intersection ym (varTypes y)
             -- ks must be a subset of js
             guard (IntSet.isSubsetOf (IntSet.fromList ks) (IntSet.fromList js))
             let vs = map (ybinds !!) js
             y2 <- lift $ scLambdaList sc vs y
             let (my3, m') = insertLookup i y2 m
             case my3 of
               Nothing -> return (MatchState m' cs)
               Just y3 -> if y2 == y3 then return (MatchState m' cs) else mzero
        Nothing ->
          case (unwrapTermF x, unwrapTermF y) of
            -- check that neither x nor y contains bound variables less than `depth`
            (FTermF xf, FTermF yf) ->
              case zipWithFlatTermF (match xenv yenv ybinds) xf yf of
                Nothing -> mzero
                Just zf -> Foldable.foldl (>=>) return zf s
            (App x1 x2, App y1 y2) ->
              do s' <- match xenv yenv ybinds x1 y1 s
                 match xenv yenv ybinds x2 y2 s'
            (Lambda xv xt xbody, Lambda yv yt ybody) ->
              do s' <- match xenv yenv ybinds xt yt s
                 match (consVarCtx xv xenv) (consVarCtx yv yenv) ((yv, yt) : ybinds) xbody ybody s'
            (Pi xv x1 x2, Pi yv y1 y2) ->
              do s' <- match xenv yenv ybinds x1 y1 s
                 match (consVarCtx xv xenv) (consVarCtx yv yenv) ((yv, y1) : ybinds) x2 y2 s'
            (Variable xv _, Variable yv _) ->
              case (lookupVarCtx xv xenv, lookupVarCtx yv yenv) of
                (Just xj, Just yj) | xj == yj -> pure s
                (Nothing, Nothing) | xv == yv -> pure s
                _ -> mzero
            (_, _) ->
              -- other possible matches include constants
              if x == y then pure s else mzero

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
       Just [_, x, y] -> mkRewriteRule vars x y False False ann
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

mkRewriteRule :: [(VarName, Term)] -> Term -> Term -> Bool -> Bool -> Maybe a -> RewriteRule a
mkRewriteRule c l r shallow convFlag ann =
    RewriteRule
    { ctxt = c
    , lhs = l
    , rhs = r
    , permutative = rulePermutes c l r
    , shallow = shallow
    , convertible = convFlag
    , annotation = ann
    }

-- | Converts a universally quantified equality proposition between the
-- two given terms to a RewriteRule.
ruleOfTerms :: Term -> Term -> RewriteRule a
ruleOfTerms l r = mkRewriteRule [] l r False False Nothing

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
    eqRule x y = pure $ Just $ mkRewriteRule [] x y False False ann

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
scExpandRewriteRule sc (RewriteRule ctxt lhs rhs _ shallow convFlag ann) =
  case R.asLambda rhs of
  Just (nm, tp, body) ->
    do let ctxt' = ctxt ++ [(nm, tp)]
       var0 <- scVariable sc nm tp
       lhs' <- scApply sc lhs var0
       pure $ Just [mkRewriteRule ctxt' lhs' body shallow convFlag ann]
  Nothing ->
    case rhs of
    (R.asRecordValue -> Just m) ->
      do let mkRule (k, x) =
               do l <- scRecordSelect sc lhs k
                  return (mkRewriteRule ctxt l x shallow convFlag ann)
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
                  let ss = addRule (mkRewriteRule ctxt rhs lhs shallow convFlag Nothing) emptySimpset
                  (_,rhs') <- rewriteSharedTerm sc (ss :: Simpset ()) rhs3
                  return (mkRewriteRule ctxt' lhs' rhs' shallow convFlag ann)
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
         scExpandRewriteRules sc [mkRewriteRule [] lhs rhs False True Nothing]
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

data Convertibility = AllRules | ConvertibleRulesOnly

type RewriterCache = IntCache IO Term

-- | Rewriter for shared terms.  The annotations of any used rules are collected
--   and returned in the result set.
rewriteSharedTerm :: forall a. Ord a => SharedContext -> Simpset a -> Term -> IO (Set a, Term)
rewriteSharedTerm sc ss t0 =
    do cache <- newIntCache
       let ?cache = cache
       setRef <- newIORef mempty
       let ?annSet = setRef
       t <- rewriteAll AllRules t0
       anns <- readIORef setRef
       pure (anns, t)

  where

    rewriteAll :: (?cache :: RewriterCache, ?annSet :: IORef (Set a)) => Convertibility -> Term  -> IO Term
    rewriteAll convertibleFlag t =
      useIntCache ?cache (termIndex t) $
      do let tf = unwrapTermF t
         tf' <- rewriteTermF convertibleFlag tf
         -- Optimization: Avoid calling scTermF to reconstruct an identical term
         let same = (fmap termIndex tf' == fmap termIndex tf)
         t' <- if same then pure t else scTermF sc tf'
         rewriteTop convertibleFlag t'

    rewriteTermF :: (?cache :: RewriterCache, ?annSet :: IORef (Set a)) =>
                    Convertibility -> TermF Term -> IO (TermF Term)
    rewriteTermF convertibleFlag tf =
        case tf of
          FTermF ftf -> FTermF <$> rewriteFTermF convertibleFlag ftf
          App e1 e2 ->
              do t1 <- scTypeOf sc e1
                 t1' <- scWhnf sc t1
                 case unwrapTermF t1' of
                   -- If type of e1 is not a dependent type, we can use any rule to rewrite e2
                   -- otherwise, we only rewrite using convertible rules
                   -- This prevents rewriting e2 from changing type of @App e1 e2@.
                   Pi x _ t
                     | IntSet.notMember (vnIndex x) (freeVars t) ->
                         App <$> rewriteAll convertibleFlag e1 <*> rewriteAll convertibleFlag e2
                   _ -> App <$> rewriteAll convertibleFlag e1 <*> rewriteAll ConvertibleRulesOnly e2
          Lambda x t1 t2 ->
            do var <- scVariable sc x t1 -- we don't rewrite t1 which represents types
               t2' <- scInstantiate sc (IntMap.singleton (vnIndex x) var) t2
               t2'' <- rewriteAll convertibleFlag t2'
               pure (Lambda x t1 t2'')
          Constant{}     -> return tf
          Variable{}     -> return tf
          Pi x t1 t2 ->
            do t1' <- rewriteAll convertibleFlag t1
               var <- scVariable sc x t1'
               t2' <- scInstantiate sc (IntMap.singleton (vnIndex x) var) t2
               t2'' <- rewriteAll convertibleFlag t2'
               pure (Pi x t1' t2'')

    rewriteFTermF :: (?cache :: RewriterCache, ?annSet :: IORef (Set a)) =>
                     Convertibility -> FlatTermF Term -> IO (FlatTermF Term)
    rewriteFTermF convertibleFlag ftf =
        case ftf of
          UnitValue        -> return ftf
          UnitType         -> return ftf
          PairValue{}      -> traverse (rewriteAll convertibleFlag) ftf
          PairType{}       -> traverse (rewriteAll convertibleFlag) ftf
          PairLeft{}       -> traverse (rewriteAll convertibleFlag) ftf
          PairRight{}      -> traverse (rewriteAll convertibleFlag) ftf
          Recursor{}       -> return ftf
          RecordType{}     -> traverse (rewriteAll convertibleFlag) ftf
          RecordValue{}    -> traverse (rewriteAll convertibleFlag) ftf
          RecordProj{}     -> traverse (rewriteAll convertibleFlag) ftf
          Sort{}           -> return ftf
          ArrayValue t es  -> ArrayValue t <$> traverse (rewriteAll convertibleFlag) es -- specifically NOT rewriting type, only elts
          StringLit{}      -> return ftf

    filterRulesFlag :: Convertibility -> Bool -> Bool
    filterRulesFlag convertibleFlag isConvertible =
      case convertibleFlag of
        ConvertibleRulesOnly -> isConvertible
        AllRules -> True

    filterRules :: Convertibility -> Either (RewriteRule a) Conversion -> Bool
    filterRules convertibleFlag (Left RewriteRule{convertible = ruleConvFlag}) =
      filterRulesFlag convertibleFlag ruleConvFlag
    filterRules convertibleFlag (Right (Conversion convConvFlag _)) =
      filterRulesFlag convertibleFlag convConvFlag

    rewriteTop :: (?cache :: RewriterCache, ?annSet :: IORef (Set a)) => Convertibility -> Term -> IO Term
    rewriteTop convertibleFlag t =
      do mt <- reduceSharedTerm sc t
         case mt of
           Nothing -> let filteredRules = filter (filterRules convertibleFlag) (Net.match_term ss (termPat t)) in
              apply convertibleFlag filteredRules t
           Just t' -> rewriteAll convertibleFlag t'

    recordAnn :: (?annSet :: IORef (Set a)) => Maybe a -> IO ()
    recordAnn Nothing  = return ()
    recordAnn (Just a) = modifyIORef' ?annSet (Set.insert a)

    apply :: (?cache :: RewriterCache, ?annSet :: IORef (Set a)) =>
             Convertibility -> [Either (RewriteRule a) Conversion] -> Term -> IO Term
    apply _ [] t = return t
    apply convertibleFlag (Left (RewriteRule {ctxt, lhs, rhs, permutative, shallow, annotation}) : rules) t = do
      -- if rewrite rule
      result <- scMatch sc ctxt lhs t
      case result of
        Nothing -> apply convertibleFlag rules t
        Just inst
          | lhs == rhs ->
            -- This should never happen because we avoid inserting
            -- reflexive rules into simp sets in the first place.
            do
               lhs' <- ppTerm sc PPS.defaultOpts lhs
               putStrLn $ "rewriteSharedTerm: skipping reflexive rule " ++
                          "(THE IMPOSSIBLE HAPPENED!): " ++ lhs'
               apply convertibleFlag rules t
          | IntMap.keysSet inst /= IntSet.fromList (map (vnIndex . fst) ctxt) ->
            do
               lhs' <- ppTerm sc PPS.defaultOpts lhs
               putStrLn $ "rewriteSharedTerm: invalid lhs does not contain all variables: "
                 ++ lhs'
               apply convertibleFlag rules t
          | permutative ->
            do
              t' <- scInstantiate sc inst rhs
              case termWeightLt t' t of
                True -> recordAnn annotation >> rewriteAll convertibleFlag t' -- keep the result only if it is "smaller"
                False -> apply convertibleFlag rules t
          | shallow ->
            -- do not to further rewriting to the result of a "shallow" rule
            do recordAnn annotation
               scInstantiate sc inst rhs
          | otherwise ->
            do recordAnn annotation
               rewriteAll convertibleFlag =<< scInstantiate sc inst rhs
    -- instead of syntactic rhs, has a bit of code that rewrites lhs (Term -> Maybe Term)
    apply convertibleFlag (Right conv : rules) t =
        do 
          case runConversion conv t of
             Nothing -> apply convertibleFlag rules t
             Just tb -> rewriteAll convertibleFlag =<< OT.complete sc tb


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
   cache <- newIntCache

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
  IntCache IO (HoistIfs s) ->
  Term ->
  IO (HoistIfs s)
doHoistIfs sc ss hoistCache = go

 where go :: Term -> IO (HoistIfs s)
       go t = useIntCache hoistCache (termIndex t) $ top t (unwrapTermF t)

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
