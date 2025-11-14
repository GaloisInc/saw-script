{- |
Module      : SAWScript.Search
Description : Namespace search for saw-script.
License     : BSD3
Maintainer  : dholland
Stability   : provisional
-}

{-# LANGUAGE OverloadedStrings #-}

module SAWScript.Search (
    SearchPattern,
    compileSearchPattern,
    matchSearchPattern
 ) where

import Data.Functor.Classes(Eq1(..), Ord1(..)) -- for liftEq, liftCompare
import Data.Text (Text)
import Data.List (sortBy)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import qualified SAWSupport.ScopedMap as ScopedMap
import SAWCentral.AST
import SAWCentral.ASTUtil (namedTyVars)
import SAWCentral.Value (TyEnv)
import SAWScript.Panic (panic)

--
-- Type matching for :search.
--
-- The idea with :search is that it's like Coq's search: you give it
-- some things to look for and it searches the current symbol table
-- for objects that mention those things. Because (in saw-script at
-- least) we aren't in Coq's dependently-typed world and we have
-- stratified values and types, and because most of what we want to
-- search for will be builtins that have no actual body to examine,
-- the things we look for will be types.
--
-- The type pattern is therefore an optional forall quantifier (using
-- the SAW/Cryptol {a} syntax) followed by one or more types. We use
-- both forall-bound and unbound/free type variables in the pattern
-- for matching purposes. Type variables that are externally bound
-- (typedef names, abstract types) are treated as literal search
-- terms. The pattern will match any type that mentions all the things
-- in the pattern.
--
-- Searching for [a] -> a will match e.g. sum : [Int] -> Int and head :
-- {t} [t] -> t, but not length : {t} [t] -> Int. In the first case
-- Int is a consistent substitution for a, and the type [a] -> a is
-- mentioned; in the second case t is a consistent substitution. In
-- the third case there isn't a consistent substitution.
--
-- Searching for {a} [a] -> a will only match {t} [t] -> t (of those
-- cases) because it requires a forall-bound variable as a the
-- substitution for a.
--
-- Currently searching for [a] [b] will still match sum, because
-- Int for both a and b is a consistent substitution. This is not
-- entirely desirable behavior but it seem difficult to avoid.
--
-- How it works:
--
-- I'm not interested in chasing after higher-order unification in
-- depth, at least for now, because it's a big deal, so the match
-- strategy we use is as follows:
--
-- 1. Match each type in the pattern against the observed ("target")
-- type. If any of them fail, we don't match.
--
-- 2. A type in the pattern matches (overall) if it matches (exactly)
-- either the target type or a subcomponent of the target type.
--
-- 3. As we go we collect mappings between the tyvars in the pattern
-- and the tyvars appearing in the target type. There can be multiple
-- such mappings because there's more than one possible way for a type
-- to match a pattern fragment. Each one of these is a Candidate.
--
-- 4. A type that's a type var in the foralls of the pattern can only
-- match a type var that's forall-bound in the target type's
-- scheme. If we don't have an entry for it in the forall mapping yet,
-- add one; if we do and it doesn't match, fail.
--
-- 5. A type that's a type var in the free type variables of the pattern
-- can match any type, but only one. If we don't have an entry for it
-- in the freeVars mapping yet, add one; if we do and it doesn't match,
-- fail.
--
-- 6. A type that's a previously bound type var must match exactly.
--
-- FUTURE: maybe we should expand all typedefs before matching...


-- "Compiled" pattern. Opaque outside this module.
data SearchPattern = SearchPattern {
    spForalls :: Set Name,   -- ^ forall-bound tyvars in the pattern
    spFreeVars :: Set Name,  -- ^ free tyvars in the pattern
    spTypes :: [Type]        -- ^ types appearing in the pattern
 }

-- Panic if we see a unification var; they aren't supposed to escape
-- the typechecker.
unifyVarPanic :: Text -> Text -> a
unifyVarPanic who what =
    panic ("search / " <> who) [what <> " contained a unification var"]

------------------------------------------------------------
-- Exact matching

-- | Match two types exactly (no alpha equivalence, no substitutions, etc.)
--
-- This could be just (==) but we deliberately don't want an Eq instance
-- for types as it's an invitation for mistakes.
matchExact :: Type -> Type -> Bool
matchExact ty1 ty2 = case (ty1, ty2) of
    (TyCon _pos1 ctor1 args1, TyCon _pos2 ctor2 args2) ->
        ctor1 == ctor2 &&
        length args1 == length args2 &&
        liftEq matchExact args1 args2
    (TyRecord _pos1 members1, TyRecord _pos2 members2) ->
        -- member maps must be equivalent via matchExact
        liftEq matchExact members1 members2
    (TyVar _pos1 a1, TyVar _pos2 a2) ->
        a1 == a2
    (TyUnifyVar _pos1 a1, TyUnifyVar _pos2 a2) ->
        a1 == a2
    (TyCon _ _ _, _) ->
        False
    (TyRecord _ _, _) ->
        False
    (TyVar _ _, _) ->
        False
    (TyUnifyVar _ _, _) ->
        False


------------------------------------------------------------
-- Substitutions

-- | A single match candidate
--
-- We accumulate substitutions for the forall-bound and free type
-- variables in the pattern; because of things like matching a tuple
-- against a scalar pattern (where several of the tuple elements might
-- match and they aren't necessarily all the same) there can be more
-- than one candidate substitution consistent with what we've seen so
-- far.
data Candidate = Candidate {
    cForallSubst :: Map Name Name,
    cFreeVarSubst :: Map Name Type
 }

-- | The starting (empty) candidate.
emptyCandidate :: Candidate
emptyCandidate = Candidate {
    cForallSubst = Map.empty,
    cFreeVarSubst = Map.empty
 }

-- | Two match candidates are the same if the types in them are the
-- same under matchExact.
--
-- The substitutions in the candidates are fragments of the target
-- type (not the pattern) so they will always have the same spelling
-- as other fragments of the target type, and we don't have to mod
-- by alpha-equivalence.
instance Eq Candidate where
    c1 == c2 =
        cForallSubst c1 == cForallSubst c2
        && liftEq matchExact (cFreeVarSubst c1) (cFreeVarSubst c2)

-- | In order to have a Set we also need an Ord instance, and since
-- there's no Ord for types we end up needing to make one up. The
-- semantics of the ordering doesn't matter; it just needs to be
-- self-consistent. (Also we need to not accidentally expose it;
-- we can't just make an Ord instance for Type.)
--
-- Note that the Type ordering needs to be (and is supposed to be)
-- consistent with matchExact. That is:
--    forall ty1 ty2. compareType ty1 ty2 == Eq <-> matchExact ty1 ty2
-- so that
--    forall c1 c2. compare c1 c2 == Eq <-> c1 == c2
--
instance Ord Candidate where
    compare c1 c2 =
        compare (cForallSubst c1) (cForallSubst c2) <>
        liftCompare compareType (cFreeVarSubst c1) (cFreeVarSubst c2)
          where
            compareType ty1 ty2 = case (ty1, ty2) of
                (TyCon _pos1 ctor1 args1, TyCon _pos2 ctor2 args2) ->
                    compare ctor1 ctor2 <>
                    liftCompare compareType args1 args2
                (TyCon _ _ _, TyRecord _ _) -> LT
                (TyCon _ _ _, TyVar _ _) -> LT
                (TyCon _ _ _, TyUnifyVar _ _) -> LT
                (TyRecord _ _, TyCon _ _ _) -> GT
                (TyRecord _pos1 fields1, TyRecord _pos2 fields2) ->
                    liftCompare compareType fields1 fields2
                (TyRecord _ _, TyVar _ _) -> LT
                (TyRecord _ _, TyUnifyVar _ _) -> LT
                (TyVar _ _, TyCon _ _ _) -> GT
                (TyVar _ _, TyRecord _ _) -> GT
                (TyVar _pos1 x1, TyVar _pos2 x2) ->
                    compare x1 x2
                (TyVar _ _, TyUnifyVar _ _) -> LT
                (TyUnifyVar _ _, TyCon _ _ _) -> GT
                (TyUnifyVar _ _, TyRecord _ _) -> GT
                (TyUnifyVar _ _, TyVar _ _) -> GT
                (TyUnifyVar _pos1 x1, TyUnifyVar _pos2 x2) ->
                    compare x1 x2


-- | For a group of match candidates, use Set. This is not free, since
-- it will exercise matchExact a lot, but it also means that we don't
-- produce exponentially many identical candidates in simple cases.
type Candidates = Set Candidate

-- | Context for matching
--
-- This is the immutable stuff generated up front; pass it around in
-- a bundle to keep things simpler.
--
data Match = Match {
    mPatForalls :: Set Name,  -- ^ forall-bound tyvars in the match pattern
    mPatFreeVars :: Set Name, -- ^ free tyvars in the match pattern
    mTgtForalls :: Set Name   -- ^ forall-bound tyvars in the match target
 }


------------------------------------------------------------
-- Selectivity

-- | Compare two type pattern fragments by how selective they are.
-- Approximately.
--
-- The idea is just to apply things that will reject a lot of
-- inputs first, not to be particularly sophisticated, so what
-- we'll do is score the patterns by whether they match one
-- thing, a few things, a lot of things, or everything (which
-- we'll manifest as the values 1-4).
--
-- More selective is "greater than", so sortBy will put the most
-- selective patterns last, so they get applied first by foldr.
--
compareBySelectivity :: Match -> Type -> Type -> Ordering
compareBySelectivity ctx ty1 ty2 =
  -- score is 1..4 where 1 is most selective, but we want
  -- more selective to be Gt, so flip the comparison.
  compare (score ty2) (score ty1)
    where
      score :: Type -> Int
      score ty = case ty of
          TyCon _pos _ctor args ->
              -- take the max score of the args, deduct one,
              -- clamp to 1
              max 1 ((foldr max 1 $ map score args) - 1)
          TyRecord _pos fields ->
              -- same treatment
              max 1 ((foldr max 1 $ map score $ Map.elems fields) - 1)
          TyVar _pos x
           | x == "_" ->
              -- wildcard matches everything
              4
           | Set.member x (mPatFreeVars ctx) ->
              -- free var matches anything
              3
           | otherwise ->
              -- forall-bound var, treat as "one thing"
              -- (even though it's not quite)
              -- or previously-bound var, which is one thing
              1
          TyUnifyVar _pos _x ->
              unifyVarPanic "compareBySelectivity" "pattern"


------------------------------------------------------------
-- Full matching

-- Match types according to a current substitution, on the assumption
-- that the target type and pattern must correspond fully.
--
-- The patterns we start out with are fragments and can match part of
-- a target, but once we start matching the target we don't want to
-- skip over internal parts of it.

-- | Match a single target type against a single pattern type, given
-- a single candidate substitution. Return an updated candidate or
-- Nothing on match failure.
--
matchFullOnce :: Match -> Candidate -> Type -> Type -> Maybe Candidate
matchFullOnce ctx cand tgtType patType =
  case patType of
      TyCon _patpos patCtor patArgs ->
          -- The pattern is a type constructor; only accept the same one.
          case tgtType of
              TyCon _tgtpos tgtCtor tgtArgs | tgtCtor == patCtor ->
                  -- If the pattern has more args, give up; if it has
                  -- the same or fewer, match the ones that are there.
                  if length tgtArgs < length patArgs then Nothing
                  else
                      -- all the args must match
                      matchFullAllPairs ctx cand (zip tgtArgs patArgs)
              _ -> Nothing

      TyRecord _patpos patFields ->
          -- The pattern is a record; only accept records. Match the
          -- fields that exist in the pattern and accept others.
          -- (FUTURE: if we ever get support for record inference and
          -- with it partial record types, we can refine this.)
          case tgtType of
              TyRecord _tgtpos tgtFields ->
                  let combine t p = (t, p)
                      pairs = Map.intersectionWith combine tgtFields patFields
                  in
                  -- all the fields must match
                  matchFullAllPairs ctx cand (Map.elems pairs)
              _ -> Nothing

      TyVar _patpos patVar
        | patVar == "_" ->
              -- wildcard matches anything, go on
              Just cand

        | Set.member patVar (mPatFreeVars ctx) ->
              -- pattern is a free var
              let fvSubst = cFreeVarSubst cand in
              case Map.lookup patVar fvSubst of
                  Nothing ->
                      -- no mapping yet, capture it
                      let fvSubst' = Map.insert patVar tgtType fvSubst
                          cand' = cand { cFreeVarSubst = fvSubst' }
                      in
                      Just cand'
                  Just prev ->
                      -- check that the mapping is identical
                      --
                      -- (note that because prev comes from the
                      -- target, any forall-bound vars or whatnot in
                      -- it must match identically and we don't have
                      -- to worry about alpha-equivalence or other
                      -- matching concerns)
                      if matchExact prev tgtType then
                          Just cand
                      else
                          Nothing

        | Set.member patVar (mPatForalls ctx) ->
              -- pattern is a forall-bound var; only accept a target
              -- forall-bound var
              case tgtType of
                  TyVar _tgtpos tgtVar | Set.member tgtVar (mTgtForalls ctx) ->
                      -- both forall-bound vars
                      let fSubst = cForallSubst cand in
                      case Map.lookup patVar fSubst of
                          Nothing ->
                              -- no mapping yet, capture it
                              let fSubst' = Map.insert patVar tgtVar fSubst
                                  cand' = cand { cForallSubst = fSubst' }
                              in
                              Just cand'
                          Just prev
                            | prev == tgtVar ->
                                  -- same var
                                  Just cand
                            | otherwise ->
                                  -- different, so we fail
                                  Nothing
                  _ -> Nothing

        | otherwise ->
              -- bound type variable; only accept matching bound type variable
              case tgtType of
                  TyVar _tgtpos tgtVar | tgtVar == patVar ->
                      Just cand
                  _ ->
                      Nothing

      TyUnifyVar _patpos _patVar ->
          unifyVarPanic "matchFullOnce" "pattern"

-- | Run matchFullOnce on a list of target and pattern type pairs.
--
-- All must match, so we thread a single candidate through all the
-- matches and give up if any of them fail.
--
-- This is the recursive case used for record members and constructor
-- arguments.
--
matchFullAllPairs :: Match -> Candidate -> [(Type, Type)] -> Maybe Candidate
matchFullAllPairs ctx cand0 pairs =
    let once (tgtType, patType) maybeCand = case maybeCand of
          Nothing -> Nothing
          Just cand -> matchFullOnce ctx cand tgtType patType
    in foldr once (Just cand0) pairs


------------------------------------------------------------
-- Fragment matching

-- Match a target type against a pattern, trying to find a subsection
-- of the target type that the pattern successfully matches. Since in
-- general there are many possible alignments, produces a set of
-- candidate substitutions.

-- | Try matching each subelement of one target type against one
-- pattern type, with one current match candidate; return possibly
-- several updated match candidates, or none on complete match
-- failure.
--
matchFragOnceBody :: Match -> Candidate -> Type -> Type -> Candidates
matchFragOnceBody ctx cand tgtType patType =
    let checkOnce tgtSub =
            matchFragOnce ctx cand tgtSub patType
        checkList tgtSubs =
            -- each result is a candidate set, the overall result is the union
            Set.unions $ map checkOnce tgtSubs
    in case tgtType of
        TyCon _tgtpos _tgtCtor tgtArgs ->
            -- The target is a type constructor; we can match any argument.
            checkList tgtArgs
        TyRecord _tgtpos tgtFields ->
            -- The target is a record. We can match any field.
            checkList (Map.elems tgtFields)
        TyVar _ _ ->
            -- The target is a variable. There aren't any subelements.
            Set.empty
        TyUnifyVar _tgtpos _tgtVar ->
            unifyVarPanic "matchFragOnceBody" "target"

-- | Match one observed ("target") type against one pattern type, with
-- one current match candidate; return possibly several updated match
-- candidates, or none on complete match failure.
--
matchFragOnce :: Match -> Candidate -> Type -> Type -> Candidates
matchFragOnce ctx cand tgtType patType =
  let whenHere = matchFullOnce ctx cand tgtType patType
      whenSub = matchFragOnceBody ctx cand tgtType patType
  in case whenHere of
      Nothing -> whenSub
      Just s -> Set.insert s whenSub

-- | Match one target type against a list of pattern type fragments.
--
matchFragList :: Match -> Candidate -> Type -> [Type] -> Candidates
matchFragList ctx cand0 tgtType patTypes =
    let oneCandidate patType cand =
            matchFragOnce ctx cand tgtType patType
        oneType patType cands =
            -- each result is a candidate set, ultimate result is the union
            let results = map (oneCandidate patType) $ Set.elems cands in
            Set.unions results
        -- Sort the pattern types so the most specific ones come last,
        -- to cut down the search space as fast as possible.
        --
        -- (Note: last rather than first because we're using foldr, not
        -- foldl.)
        patTypes' = sortBy (compareBySelectivity ctx) patTypes
    in
    foldr oneType (Set.singleton cand0) patTypes'


------------------------------------------------------------
-- External interface

-- | Check and compile a type schema pattern.
--
-- We get passed a list of forall bindings (will often be empty)
-- and one or more types. Convert this into our internal representation.
--
-- Type variables that are not explicitly forall-bound and not listed
-- in the environment are handled as free type variables, which have
-- different match semantics from forall-bound type variables. See
-- notes at the top of the file.
--
compileSearchPattern :: TyEnv -> SchemaPattern -> SearchPattern
compileSearchPattern tyEnv (SchemaPattern forallList tys) =
  let foralls = Set.fromList $ map (\(_pos, name) -> name) forallList
      boundVars = ScopedMap.allKeysSet tyEnv
      -- treat '_' as a bound var to avoid assorted confusion
      boundVars' = Set.insert "_" boundVars
      oneType ty freeVarsSoFar =
        -- get all the type variables present and drop the ones already known
        let vars0 = Map.keysSet $ namedTyVars ty
            vars1 = vars0 Set.\\ foralls
            vars2 = vars1 Set.\\ boundVars'
            vars3 = vars2 Set.\\ freeVarsSoFar
        in
        -- add what's left to the collection of free type variables
        Set.union freeVarsSoFar vars3
      freeVars = foldr oneType Set.empty tys
  in
  SearchPattern { spForalls = foralls, spFreeVars = freeVars, spTypes = tys }

-- | Match a type pattern.
--
matchSearchPattern :: SearchPattern -> Schema -> Bool
matchSearchPattern pattern (Forall tgtForallList tgtType) =
  let tgtForalls = Set.fromList $ map (\(_pos, name) -> name) tgtForallList
      ctx = Match {
          mPatForalls = spForalls pattern,
          mPatFreeVars = spFreeVars pattern,
          mTgtForalls = tgtForalls
       }
      cands = matchFragList ctx emptyCandidate tgtType (spTypes pattern)
  in
  not $ Set.null cands
