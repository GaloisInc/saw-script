{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}

{- |
Module      : SAWCoreLean.Signature
Copyright   : Galois, Inc. 2026
License     : BSD3
Maintainer  : saw@galois.com
Stability   : experimental
Portability : portable

What an emitted declaration DECLARES: the Lean-side binder and
universe plumbing every emission path shares, and the telescope
fingerprint that compares a declared signature against the SAWCore
type it claims to express.

FAMILY-3 CHOKEPOINT. The annotation invariant this module exists to
hold is stated in @doc/2026-07-29_annotation-invariant.md@: the
emitted signature must derive from the same authority as the emitted
body. Extracted from "SAWCoreLean.Term" in the 2026-07-29 Family-3
split so that the invariant has one named home rather than being a
property distributed over a 5,600-line file.
-}

module SAWCoreLean.Signature
  ( importedRealizationAliasIdent
  , combineBinders
  , mkDefinitionWith
  , usedUniversesInDecl
  , usedUniversesInBinder
  , usedUniversesInPiBinder
  , usedUniversesInSort
  , usedUniversesInLevel
  , usedUniversesInTerm
  , leanPiSpineArity
  , leanPiSpineBinderTypes
  , leanSortBinders
  , leanExceptCarriedGoalBinders
  , TelescopeFp(..)
  , sawBinderFp
  , leanBinderFp
  , telescopeFpMismatch
  , topLevelDefConvention
  , AnnotationAdjustment(..)
  , applyAnnotationAdjustment
  , wrappedArrowAdjustment
  ) where

import qualified Data.Set                     as Set
import           Data.Set                     (Set)
import qualified Data.Text                    as Text
import           Prelude                      hiding (fail)
import           Text.Encoding.Z              (zEncodeString)

import qualified Language.Lean.AST            as Lean
import           Language.Lean.Pretty         (anonymizeUnusedPiBinders)

import           SAWCore.Name
import           SAWCore.Recognizer
import           SAWCore.SharedTerm

import           SAWCoreLean.Convention
import           SAWCoreLean.Calculus


importedRealizationAliasIdent :: Name -> Lean.Ident
importedRealizationAliasIdent nm =
  Lean.Ident $
    "__saw_realizes_" ++
    zEncodeString (Text.unpack (toAbsoluteName (nameInfo nm)))

-- | Combine a term-level 'Binder' with a type-level 'PiBinder',
-- keeping the binder's identifier (the body references it by name)
-- but the pi's implicit/explicit status AND the pi's type. Mirrors
-- @SAWCoreRocq.Term.combineBinders@.
--
-- Audit-2 F-8, fixed 2026-07-25 by CONSTRUCTION rather than by a
-- gate. This used to keep the LAMBDA's type annotation and discard
-- the Pi's, so the emitted @def@'s declared signature was synthesized
-- from the BODY side while the term's declared type came from the
-- TYPE side. The two are produced by separate predicates that the
-- code says can disagree, and a disagreement gave the emitted
-- declaration a different type from the SAWCore term it claims to
-- translate — silently, since Lean has no way to know the SAWCore
-- type.
--
-- Taking the Pi's type removes the possibility instead of detecting
-- it: the declared type IS the authority for what the definition's
-- type is, so the emitted signature now has the SAWCore term's type
-- by construction. A genuine disagreement becomes a Lean type error
-- (the body no longer matches the signature) — loud, and checked by
-- the kernel rather than by us.
--
-- A gate was tried first and rejected: comparing the two renderings
-- flags differences that are not disagreements at all (the body and
-- type traversals draw fresh universe variables from one counter, so
-- @Eq__rec@'s motive renders @Sort u1@ against @Sort u3@; and an
-- anonymous Pi binder renders against an unused named one, as in
-- @eq_cong@). Getting that right needs a full structural
-- alpha-equivalence, which is delicate code in a trust path to
-- detect a condition this line makes unreachable.
--
-- Dropping the body-side annotation is the established pattern here,
-- not a new one: the unequal-length branch below already strips
-- lambda annotations wholesale and relies on the signature.
combineBinders :: Lean.Binder -> Lean.PiBinder -> Lean.Binder
combineBinders (Lean.Binder _ n _) (Lean.PiBinder impl _ ty) =
  Lean.Binder impl n (Just ty)

-- | Produce a Lean @def@ from a 'Noncomputable' flag, a list of
-- universe-variable names, a name, a translated body, and a
-- translated type. The universe list is filtered to what the
-- emitted decl actually mentions — the type and body are translated
-- separately and may independently allocate universe variables that
-- get shadowed when Lambda binders hoist into the @def@ signature.
-- Declaring only the referenced ones matches what Lean expects.
--
-- If the body is a lambda and the type is a matching pi, the
-- binders are hoisted into the @def@ signature for readability.
--
-- If the body is a 'Lambda' with more binders than the type has
-- 'Pi' binders, or vice versa, the surplus stays in the body /
-- type as-is. Crucially, we strip the /type annotations/ from the
-- body's outer lambdas when the signature already supplies them —
-- otherwise Lean re-elaborates the annotated binder against the
-- signature's binder, and the body-side's universe variables go
-- unused (they're only referenced by the redundant annotation
-- Lean ignores).
mkDefinitionWith ::
  Lean.Noncomputable -> [String] ->
  Lean.Ident -> Lean.Term -> Lean.Term -> Lean.Decl
mkDefinitionWith nc univs name body tp =
  let raw = case (body, tp) of
        (Lean.Lambda bs t, Lean.Pi bs' tp')
          | length bs == length bs' ->
              -- Lengths match: hoist lambda binders into signature.
              Lean.Definition nc [] name (zipWith combineBinders bs bs')
                              (Just tp') t
          | length bs < length bs' ->
              -- Body has fewer lambdas than type has pi binders.
              -- Emit the body alone (the remaining pi binders stay
              -- in the signature's type).
              Lean.Definition nc [] name [] (Just tp)
                              (Lean.Lambda (map stripType bs) t)
        _ -> Lean.Definition nc [] name [] (Just tp) body
      used = usedUniversesInDecl raw
      keep = filter (`Set.member` used) univs
  in rebrandUnivs keep raw
  where
    rebrandUnivs us (Lean.Definition nc' _ nm bs mty bd) =
      Lean.Definition nc' us nm bs mty bd
    rebrandUnivs _ d = d

    -- | Drop the type annotation from a lambda binder. Lean will
    -- infer the type from the surrounding @def@'s pi signature.
    stripType :: Lean.Binder -> Lean.Binder
    stripType (Lean.Binder impl n _) = Lean.Binder impl n Nothing

-- | Collect every universe-variable name mentioned in a 'Lean.Decl'
-- by walking its AST. Used to filter the per-def universe list down
-- to the variables that are actually referenced after 'mkDefinition'
-- hoists binders (the type and the body may have introduced separate
-- shadowed variables).
usedUniversesInDecl :: Lean.Decl -> Set String
usedUniversesInDecl d = case d of
  Lean.Axiom _ _ ty -> usedUniversesInTerm ty
  Lean.Definition _ _ _ bs mty bd ->
    Set.unions
      [ Set.unions (map usedUniversesInBinder bs)
      , maybe Set.empty usedUniversesInTerm mty
      , usedUniversesInTerm bd
      ]
  Lean.InductiveDecl (Lean.Inductive _ _ ps ixs s ctors) ->
    Set.unions
      [ Set.unions (map usedUniversesInBinder ps)
      , Set.unions (map usedUniversesInPiBinder ixs)
      , usedUniversesInSort s
      , Set.unions [ usedUniversesInTerm t | Lean.Constructor _ t <- ctors ]
      ]
  Lean.Namespace _ ds -> Set.unions (map usedUniversesInDecl ds)
  -- A constructor-order assertion mentions only constant names.
  Lean.CtorOrderAssertion _ _ -> Set.empty

usedUniversesInBinder :: Lean.Binder -> Set String
usedUniversesInBinder (Lean.Binder _ _ mty) =
  maybe Set.empty usedUniversesInTerm mty

usedUniversesInPiBinder :: Lean.PiBinder -> Set String
usedUniversesInPiBinder (Lean.PiBinder _ _ ty) = usedUniversesInTerm ty

usedUniversesInSort :: Lean.Sort -> Set String
usedUniversesInSort = \case
  Lean.Prop            -> Set.empty
  Lean.TypeLvl _       -> Set.empty
  Lean.TypeVar u       -> Set.singleton u
  Lean.SortVar u       -> Set.singleton u

-- | Collect universe-variable names referenced inside a
-- 'Lean.UnivLevel' (the explicit per-arg level in @\@Foo.{u, v}@).
usedUniversesInLevel :: Lean.UnivLevel -> Set String
usedUniversesInLevel = \case
  Lean.LevelVar u  -> Set.singleton u
  Lean.LevelLit _  -> Set.empty
  Lean.LevelSucc l -> usedUniversesInLevel l
  Lean.LevelMax ls -> Set.unions (map usedUniversesInLevel ls)
  Lean.LevelIMax ls -> Set.unions (map usedUniversesInLevel ls)

usedUniversesInTerm :: Lean.Term -> Set String
usedUniversesInTerm = \case
  Lean.Lambda bs t ->
    Set.unions (usedUniversesInTerm t : map usedUniversesInBinder bs)
  Lean.Pi bs t ->
    Set.unions (usedUniversesInTerm t : map usedUniversesInPiBinder bs)
  Lean.Let _ bs mty t b ->
    Set.unions
      [ Set.unions (map usedUniversesInBinder bs)
      , maybe Set.empty usedUniversesInTerm mty
      , usedUniversesInTerm t
      , usedUniversesInTerm b
      ]
  Lean.App f args ->
    Set.unions (usedUniversesInTerm f : map usedUniversesInTerm args)
  Lean.Sort s -> usedUniversesInSort s
  Lean.Var _ -> Set.empty
  Lean.ExplVar _ -> Set.empty
  Lean.ExplVarUniv _ levels ->
    Set.unions (map usedUniversesInLevel levels)
  Lean.NatLit _ -> Set.empty
  Lean.IntLit _ -> Set.empty
  Lean.List ts -> Set.unions (map usedUniversesInTerm ts)
  Lean.StringLit _ -> Set.empty
  Lean.Tactic _ -> Set.empty

-- | Translate a SAWCore 'Term' and its type to a Lean @def@, together
-- with any auxiliary declarations needed to support it (the bodies of
-- constants referenced along the way).
--
-- Emits @noncomputable def@: SAWCore primitives like @coerce@,
-- @unsafeAssert@, @error@ are axioms that Lean's code generator
-- refuses to compile, and typical normalized terms reference at
-- least one of them. Marking every user def @noncomputable@ is a
-- safe over-approximation — the goal is a file that typechecks, not
-- one that runs.
-- | Number of binders in the (greedy) Pi spine of a translated Lean
-- term — the emitted goal's quantifier telescope. Used by the
-- goal-telescope emission pin (replay design, seventh-audit
-- amendment 1, ratified 2026-07-17): the emitted telescope must
-- match the SAWCore-side Pi count, or emission REFUSES — a dropped
-- or invented quantifier at this seam is the unsoundness path.
leanPiSpineArity :: Lean.Term -> Int
leanPiSpineArity (Lean.Pi bs t) = length bs + leanPiSpineArity t
leanPiSpineArity _ = 0

-- | The emitted goal Pi spine's binder types, outermost first
-- (2026-07-18 replay hardening: the binder-TYPE half of the
-- goal-telescope pin — the arity pin alone let a same-arity
-- wrong-type binder through).
leanPiSpineBinderTypes :: Lean.Term -> [Lean.Type]
leanPiSpineBinderTypes (Lean.Pi bs t) =
  [ ty | Lean.PiBinder _ _ ty <- bs ] ++ leanPiSpineBinderTypes t
leanPiSpineBinderTypes _ = []

-- | Goal-telescope binders whose domain mentions the @Except String@
-- VALUE CARRIER, outermost first, rendered as @"name : carrier-site"@.
--
-- W2-UNRUN-1 (raised wave 2, could not be reproduced then,
-- REPRODUCED and reinstated CRITICAL by wave 3 on 2026-07-30).
--
-- THE INVARIANT THIS PINS — stated carefully, because the first cut
-- (2026-07-30) stated it too broadly and over-refused; see the
-- VALUE-IMAGE EXEMPTION below.
--
-- A goal-telescope domain is legitimately one of two things:
--
--   * a VALUE image — the type of something the goal quantifies over.
--     Under the value-function convention this may be carrier-headed
--     or a function INTO the carrier
--     (@Except String Bool -> Except String Bool@ for a SAWCore
--     @Bool -> Bool@ binder). Quantifying over a carrier-headed
--     domain ranges over MORE inhabitants than the SAWCore type, so
--     the Lean statement is STRONGER, never weaker. Safe.
--
--   * a PROPOSITION — a sequent HYPOTHESIS that @sequentToProp@
--     folded into the SAWCore arrow chain. Here carrier mentions are
--     dangerous: the hypothesis's carried image can be UNINHABITED,
--     which makes the implication vacuous and the Lean statement
--     strictly WEAKER.
--
-- So the gate reports a carrier mention only in a domain that is NOT
-- a value image, where "value image" = after peeling every Pi layer,
-- the final codomain is carrier-headed.
--
-- WHY IT IS UNSOUND, not merely odd: the hypothesis's Except-carried
-- image can be UNINHABITED. Wave 3's witness is an ordinary Cryptol
-- module (@v = [7, error "e"]@, @h = (v @@ 0) < 100@) plus
-- @goal_cut@: the emitted domain is
-- @\@Eq (Except String Bool) (…saw_throw_error…) (Pure.pure true)@,
-- and @Except.error _ = Except.ok _@ is uninhabited by constructor
-- no-confusion. The implication is therefore VACUOUSLY provable
-- while SAW independently proves the same hypothesis TRUE — so the
-- Lean theorem is strictly weaker than the obligation, and a replay
-- of it admits an arbitrary conclusion.
--
-- Why the pre-existing telescope pin did not catch it: the ARITY
-- half fires only when the ANTECEDENT contains a repeated subterm,
-- which hoists the P-1 @let@ above the Pi so 'leanPiSpineArity'
-- scores 0. A repeat in the CONSEQUENT leaves the arrow intact and
-- the goal emits. The binder-TYPE half is structurally blind here:
-- both sides fingerprint @FpOther@ and 'telescopeFpMismatch' skips
-- any position where either side is @FpOther@.
--
-- Scope is the goal's own TELESCOPE — the binders the pin governs,
-- and the only ones that become Lean hypotheses. The walk descends
-- through @Lean.Let@ to reach it: a share arising in the OUTERMOST
-- binder's domain hoists above the whole Pi
-- (@translateTermLetAt@'s @foldr mkLet@), giving @Let … (Pi …)@,
-- which a spine walk stopping at the first non-Pi would miss
-- entirely. (Not "every let is outermost" — @translateTermLetAt@
-- runs at every level and a share depending on a binder cannot
-- escape it, so @Pi … (Let …)@ is the common shape. The re-audit
-- corrected that over-generalisation.) The first cut
-- (2026-07-30) did stop there, which disarmed this gate for the
-- entire let-hoisted class; the arity half happens to refuse those
-- today, so nothing was exploitable, but the coverage was
-- ACCIDENTAL. 'leanSortBinders' already descended through @Let@ —
-- the asymmetry was the bug.
--
-- Refuse-only, like its two sibling gates: over-approximating costs
-- a rejected emission, never an admitted one.
--
-- KNOWN LIMITS, recorded rather than overclaimed. Three, and each is
-- an ARGUMENT rather than a check, so each is where the next defect
-- of this family would live:
--
--  1. This tests for the CARRIER, not for uninhabitedness. A raw
--     hypothesis domain can also be uninhabited
--     (@\@Eq Bool Bool.false Bool.true@) and emits past this gate.
--     That is faithful rather than weaker — a raw domain means the
--     same thing on both sides, so the SAWCore obligation is equally
--     vacuous — but the safety rests on "raw implies faithful".
--
--  2. The ANONYMITY test would miss a NAMED folded hypothesis.
--     @sequentToProp@ cannot produce one (@scFun@ is non-dependent),
--     so that route is closed; a route that NAMES a hypothesis
--     binder escaped — and one existed.
--
--     WAS (2026-07-30, FALSIFIED 2026-07-31): "Measured narrower
--     than it first looks: the carrier is not ADDRESSABLE from
--     SAWCore — @parse_core "Except"@ fails — so a user cannot
--     hand-write a named binder mentioning it. Every carrier
--     mention is introduced by this translator's own value
--     wrapping, and the wrapping names a binder only when the
--     SAWCore Pi it images is DEPENDENT, i.e. a quantified VALUE.
--     An escape therefore needs a new TRANSLATOR route."
--
--     The measurement was real and its FIRST clause holds. The
--     second clause was never measured, and is false: the Lean
--     binder name is copied from the SAWCore @VarName@
--     (@Convention.withSAWVar@) whether or not the Pi is dependent,
--     and @parse_core@ preserves a hand-written name. So
--     @prove_core (offline_lean …) "(h : EqTrue …) -> EqTrue …"@
--     names a NON-dependent hypothesis binder, the translator wraps
--     it into a carrier equation exactly as clause 1 concedes, and
--     TEST 1 exempted it. Demonstrated end-to-end 2026-07-31: SAW
--     proves the hypothesis and refutes the conclusion (so the
--     obligation is FALSE), the emitted goal is provable in Lean
--     with @[propext, Quot.sound]@ — both ALLOWLISTED — so replay
--     would have issued evidence for a false claim. In-model
--     CRITICAL; the anonymous spelling of the same goal was
--     refused, which is what made the asymmetry invisible.
--
--     CLOSED by making the gate inspect the binders the printer
--     emits (see 'goSpine'): the printer already anonymizes
--     named-but-unused binders, so gate and artifact can no longer
--     disagree. Pinned by
--     @saw-boundary/goal_named_hypothesis_binder@.
--
--  3. The VALUE-IMAGE test's failure direction is ADMISSION, not
--     refusal: a false positive from 'isExceptStringType' here
--     disarms the gate for that binder. It is the only sub-predicate
--     in this function with that polarity — 'carrier' and the walk
--     both fail toward over-refusal. Safety rests on "no producible
--     hypothesis image is carrier-headed", since a hypothesis image
--     is @Eq@/@EqTrue@-headed.
leanExceptCarriedGoalBinders :: Lean.Term -> [String]
leanExceptCarriedGoalBinders = goSpine
  where
    -- Inspect the binders the PRINTER EMITS, not the ones the AST
    -- happens to carry (W2-UNRUN-2 re-score fix, 2026-07-31; see
    -- limit 2 above for the falsified premise). 'prettyDecl' runs
    -- 'anonymizeUnusedPiBinders' before printing, so a named-but-
    -- UNUSED binder ships as a bare arrow; running the same function
    -- here means TEST 1's anonymity question is asked of the shipped
    -- text. Direction of the change is proceed -> reject (named
    -- non-dependent hypotheses now reach TESTs 2/3 instead of being
    -- exempted), which is the safe direction under contributing.md
    -- rule C7.
    goSpine (Lean.Pi bs t)          = concatMap piBinder (anonymizeUnusedPiBinders bs t)
                                        ++ goSpine t
    goSpine (Lean.Let _ _ _ _ body) = goSpine body
    goSpine _                       = []

    -- Two narrowing tests, both needed, both grounded. The first cut
    -- had NEITHER and refused faithful function-typed binders; the
    -- second cut had only the value-image test and still refused
    -- faithful COMPOSITE binders (a record or tuple with a function
    -- component is not carrier-headed after peeling Pis, so its
    -- wrapped components were still reported). Both were regressions
    -- on shapes that emitted before this gate existed.
    piBinder (Lean.PiBinder _ mnm ty)
      -- TEST 1, ANONYMITY — the principled one. A folded sequent
      -- hypothesis is ALWAYS an anonymous binder: @sequentToProp@
      -- builds the arrow chain with @scFun@ (Proof.hs), which makes a
      -- NON-DEPENDENT function type and so binds no name. A
      -- quantified VALUE binder, by contrast, is named — its body
      -- refers to it. So a named domain is never a folded hypothesis,
      -- whatever its type mentions.
      | Just _ <- mnm = []
      -- TEST 2, VALUE IMAGE — the backstop, for an ANONYMOUS domain
      -- that is still a value: a non-dependent SAWCore arrow
      -- @(Bool -> Bool) -> …@ emits an anonymous binder whose domain
      -- is the wrapped function image. Carrier-headed after peeling
      -- Pis means "delivers a value", which ranges over MORE
      -- inhabitants than the SAWCore type and so is stronger, not
      -- weaker.
      | isExceptStringType (finalCodomain ty) = []
      | otherwise = map (\s -> "_ : " ++ s) (goTy ty)

    -- Peel every Pi layer; what remains is what the domain ultimately
    -- delivers.
    finalCodomain (Lean.Pi _ body) = finalCodomain body
    finalCodomain t                = t

    -- Walk a TELESCOPE DOMAIN, reporting every reachable mention of
    -- the value carrier's head. Mirrors 'leanSortBinders'' @goTy@,
    -- including its total case list: a new 'Lean.Term' constructor
    -- must be classified here rather than silently ignored.
    goTy ty = case ty of
      Lean.Var nm             -> carrier (leanIdentStr nm)
      Lean.ExplVar nm         -> carrier (leanIdentStr nm)
      Lean.ExplVarUniv nm _   -> carrier (leanIdentStr nm)
      Lean.Pi bs b            ->
        concatMap (\(Lean.PiBinder _ _ t) -> goTy t) bs ++ goTy b
      Lean.Lambda bs b        ->
        concatMap (\(Lean.Binder _ _ mt) -> concatMap goTy mt) bs ++ goTy b
      Lean.Let _ bs mty rhs b ->
        concatMap (\(Lean.Binder _ _ mt) -> concatMap goTy mt) bs
          ++ concatMap goTy mty ++ goTy rhs ++ goTy b
      Lean.App f as           -> goTy f ++ concatMap goTy as
      Lean.List xs            -> concatMap goTy xs
      Lean.Sort{}             -> []
      Lean.NatLit{}           -> []
      Lean.IntLit{}           -> []
      Lean.StringLit{}        -> []
      Lean.Tactic{}           -> []

    -- The carrier's HEAD as the emitter writes it. @Except@ is in
    -- 'emitterBareNames' and emitted bare; matching on the last
    -- dotted component accepts a qualified spelling too, so a future
    -- change of emission style cannot silently disarm this gate.
    -- (ONE guard, not two: the first cut had a separate @s ==
    -- "Except"@ arm, which the last-component test already subsumes.
    -- The fix audit caught it as dead code presented as coverage.)
    carrier s
      | lastComponent s == "Except" = [s]
      | otherwise                   = []

    lastComponent = reverse . takeWhile (/= '.') . reverse

leanSortBinders :: Lean.Term -> [String]
leanSortBinders = go
  where
    go tm = case tm of
      Lean.Lambda bs b        -> concatMap binder bs ++ go b
      Lean.Pi bs b            -> concatMap piBinder bs ++ go b
      Lean.Let _ bs mty rhs b ->
        concatMap binder bs ++ concatMap go mty ++ go rhs ++ go b
      Lean.App f as           -> go f ++ concatMap go as
      Lean.List xs            -> concatMap go xs
      Lean.Sort{}             -> []
      Lean.Var{}              -> []
      Lean.ExplVar{}          -> []
      Lean.ExplVarUniv{}      -> []
      Lean.NatLit{}           -> []
      Lean.IntLit{}           -> []
      Lean.StringLit{}        -> []
      Lean.Tactic{}           -> []

    binder (Lean.Binder _ nm mty) = concatMap (report (leanIdentStr nm)) mty
    piBinder (Lean.PiBinder _ mnm ty) =
      report (maybe "_" leanIdentStr mnm) ty

    -- A binder whose TYPE mentions a sort is reported.
    --
    -- B2 (0.02 release-gate audit, 2026-07-29, CRITICAL). This used
    -- to report only when the binder's type WAS a sort, and
    -- otherwise fell through to 'go' — whose @Lean.Sort{} -> []@ arm
    -- DISCARDS. So @(f : Nat -> sort 0)@ emitted @(f : Nat -> Type)@
    -- with no diagnostic. That matters because SAWCore admits
    -- @Prop <= sort 0@ cumulativity and covariant Pi subtyping, so
    -- the SAW obligation genuinely ranges over Prop-valued @f@ while
    -- the Lean goal does not: a strictly WEAKER statement, and a
    -- well-typed artifact, so nothing downstream notices. Gate 1
    -- cannot cover it either — @sort 0@ allocates no universe
    -- variable.
    --
    -- The binder's type gets its own walk ('goTy') that REPORTS a
    -- sort wherever it occurs. Deliberately NOT applied to 'go': the
    -- goal BODY can legitimately carry a @Lean.Sort@ (a translated
    -- type argument), and reporting those would refuse emissions
    -- that are perfectly faithful.
    report nm ty = map (\s -> nm ++ " : " ++ s) (goTy ty)

    -- Walk a BINDER TYPE. Reports every non-Prop sort it can reach.
    -- Refuse-only, so over-approximating here costs a rejected
    -- emission, never an admitted one — which is the right direction
    -- for a gate whose whole purpose is that the emitted quantifier
    -- must not be narrower than SAWCore's.
    goTy ty = case ty of
      Lean.Sort Lean.Prop     -> []
      Lean.Sort s             -> [renderSort s]
      Lean.Pi bs b            ->
        concatMap (\(Lean.PiBinder _ _ t) -> goTy t) bs ++ goTy b
      Lean.Lambda bs b        ->
        concatMap (\(Lean.Binder _ _ mt) -> concatMap goTy mt) bs ++ goTy b
      Lean.Let _ bs mty rhs b ->
        concatMap (\(Lean.Binder _ _ mt) -> concatMap goTy mt) bs
          ++ concatMap goTy mty ++ goTy rhs ++ goTy b
      Lean.App f as           -> goTy f ++ concatMap goTy as
      Lean.List xs            -> concatMap goTy xs
      Lean.Var{}              -> []
      Lean.ExplVar{}          -> []
      Lean.ExplVarUniv{}      -> []
      Lean.NatLit{}           -> []
      Lean.IntLit{}           -> []
      Lean.StringLit{}        -> []
      Lean.Tactic{}           -> []

    renderSort Lean.Prop        = "Prop"
    renderSort (Lean.TypeLvl 0) = "Type"
    renderSort (Lean.TypeLvl n) = "Type " ++ show n
    renderSort (Lean.TypeVar u) = "Type " ++ u
    renderSort (Lean.SortVar u) = "Sort " ++ u

-- | Coarse TYPE-FAMILY fingerprints for the telescope pin. The
-- comparison can only REFUSE emission (never admit), so coarseness
-- is safe: 'FpOther' matches anything (var-headed and exotic types
-- stay unpinned); the concrete families must agree pointwise.
data TelescopeFp = FpVec | FpBool | FpNat | FpInt | FpFun | FpOther
  deriving (Eq, Show)

sawBinderFp :: Term -> TelescopeFp
sawBinderFp ty
  | Just _ <- asGlobalApply "Prelude.Vec" ty = FpVec
  | Just i <- asGlobalDef ty, identName i == "Bool" = FpBool
  | Just _ <- asNatType ty = FpNat
  | Just i <- asGlobalDef ty, identName i == "Integer" = FpInt
  | Just _ <- asPi ty = FpFun
  | otherwise = FpOther

leanBinderFp :: Lean.Type -> TelescopeFp
leanBinderFp ty0 = go (stripExcept ty0)
  where
    stripExcept (Lean.App (Lean.Var (Lean.Ident h)) [_, t])
      | baseName h == "Except" = t
    stripExcept t = t
    go t = case t of
      Lean.Pi{} -> FpFun
      _ -> case fst (leanAppHead t) of
        Just h | baseName h == "Vec" || baseName h == "BitVec" -> FpVec
               | baseName h == "Bool" -> FpBool
               | baseName h == "Nat"  -> FpNat
               | baseName h == "Int"  -> FpInt
        _ -> FpOther
    leanAppHead (Lean.App f _) = leanAppHead f
    leanAppHead (Lean.Var (Lean.Ident h)) = (Just h, ())
    leanAppHead (Lean.ExplVar (Lean.Ident h)) = (Just h, ())
    leanAppHead _ = (Nothing, ())
    baseName h = reverse (takeWhile (/= '.') (reverse h))

-- | Pointwise fingerprint agreement; 'FpOther' on EITHER side is a
-- wildcard. Returns the first mismatch (index, saw, lean).
telescopeFpMismatch :: [Term] -> [Lean.Type] -> Maybe (Int, TelescopeFp, TelescopeFp)
telescopeFpMismatch sawTys leanTys =
  case [ (ix, s, l)
       | (ix, (sty, lty)) <- zip [0 :: Int ..] (zip sawTys leanTys)
       , let s = sawBinderFp sty
       , let l = leanBinderFp lty
       , s /= FpOther, l /= FpOther, s /= l
       ] of
    m : _ -> Just m
    []    -> Nothing

-- | 'translateDefDoc' plus the emitted goal body's Pi-spine arity
-- (see 'leanPiSpineArity').
-- | THE top-level definition convention (calculus §Definitions;
-- 2026-07-18 exception-hunt Finding 1). Single authority for the two
-- questions every top-level emitter must answer identically: the
-- position the body stands at (runtime-value iff the declared SAW
-- type is value-domain — the body then adapts through the
-- chokepoint), and whether the type ANNOTATION wraps (value-domain
-- type, OR a wrapped-produced body at a non-wrapping type, e.g. a
-- runtime-computed Nat — annotating such a def raw cannot elaborate;
-- filed 2026-07-12, fixed 2026-07-14). The three top-level emitters
-- (translateDefDocWithArity, CryptolModule, SAWModule) had
-- hand-copied this and CryptolModule's copy had already drifted
-- (missing the wrapped-body clause) — all three now call here.
--
-- 2026-07-29 (F-1): the second component is no longer a Bool but an
-- 'AnnotationAdjustment'. A Bool can only express "wrap the whole
-- annotation", and the under-applied partial-op wrapper needs
-- "wrap the FORMALS the wrapper declares runtime, and the result" —
-- the case the Bool could not say, so the annotation was emitted raw
-- over a wrapped-arrow body. Callers apply it with
-- 'applyAnnotationAdjustment' instead of hand-rolling @wrapExcept@.
topLevelDefConvention ::
  TermTranslationMonad m =>
  Term -> TranslatedTerm -> m (Lean.Term, AnnotationAdjustment)
topLevelDefConvention tp bodyResult = do
  let wrapType = shouldWrapBinder tp
  bodyLean <- if wrapType
                 then adaptToRuntime bodyResult
                 else pure (translatedTermLean bodyResult)
  let adjustment
        | wrapType                             = AnnotateWrapped
        | BindingWrappedArrow modes <- ttShape bodyResult
                                               = wrappedArrowAdjustment tp modes
        | ttShape bodyResult == BindingWrapped = AnnotateWrapped
        | otherwise                            = AnnotateAsIs
  pure (bodyLean, adjustment)

-- | Decide, per residual formal of a partially-applied support
-- wrapper, whether the emitted annotation needs an @Except@ ADDED.
--
-- The subtlety, and the bug the first version of the F-1 fix had:
-- @translateTerm@ ALREADY wraps a Pi binder whose SAWCore type is
-- value-domain (Term.hs, @if shouldWrapBinder dom then wrapExcept …@).
-- So "the wrapper declares this slot runtime, therefore wrap it" is
-- wrong — it double-wraps every formal whose own image is already
-- wrapped, and emits @Except String (Except String (Vec n Bool))@.
-- Caught by the bare-@bvUDiv@ probe in
-- drivers/under_applied_partial_wrapper; the @divNat@ shape alone
-- could not catch it, because @shouldWrapBinder Nat@ is 'False' and
-- that formal genuinely does need the wrap added.
--
-- So the question asked here is the DIFFERENCE between what the
-- wrapper's Lean signature has and what the translated SAWCore type
-- already has. Both sides are answered by the SAME authority — the
-- wrap rule applied to the SAWCore type — which is the point of the
-- annotation invariant; nothing inspects the emitted Lean AST.
wrappedArrowAdjustment :: Term -> [ArgMode] -> AnnotationAdjustment
wrappedArrowAdjustment = go []
  where
    go acc ty [] = AnnotateWrappedArrow (reverse acc) (needsExcept ty)
    go acc ty (m : ms) = case asPi ty of
      Just (_, dom, cod) ->
        go (addFor m dom : acc) cod ms
      -- The SAWCore type has fewer binders than the wrapper has
      -- residual formals: the two authorities disagree about arity,
      -- so decline to adjust rather than invent a signature. Loud at
      -- Lean, which is the intended ordering of bad outcomes.
      Nothing -> AnnotateAsIs

    -- A runtime slot needs the wrap added only when the SAWCore
    -- binder's own image did not already carry it. Raw-family modes
    -- (a bitvector width is 'IndexArg') never do.
    addFor m dom = m == RuntimeArg && needsExcept dom
    needsExcept t = not (shouldWrapBinder t)

-- | How the emitted type ANNOTATION must be adjusted so that it
-- describes the body the translator actually produced.
--
-- This type is the Family-3 invariant in miniature
-- (@doc/2026-07-29_annotation-invariant.md@): the adjustment is
-- computed FROM the body's production record ('BindingShape'), never
-- re-derived from what the body was supposed to be. Adding a case
-- here is how a new body representation earns a faithful signature.
data AnnotationAdjustment
  = AnnotateAsIs
    -- ^ Raw: the body stands at the SAWCore type's own image.
  | AnnotateWrapped
    -- ^ @Except String T@ around the whole annotation.
  | AnnotateWrappedArrow [Bool] Bool
    -- ^ The body is a partially-applied support wrapper. One flag per
    -- residual formal, outermost first, saying whether that binder
    -- needs an @Except@ ADDED to reach the wrapper's declared slot
    -- type; the trailing flag says the same for the result. Computed
    -- by 'wrappedArrowAdjustment', which is where the reasoning about
    -- what the translated type already carries lives.
  deriving (Eq, Show)

-- | Apply an 'AnnotationAdjustment' to the translated SAWCore type.
--
-- 'AnnotateWrappedArrow' walks the Pi spine consuming one declared
-- mode per binder. If the spine runs out of binders before the modes
-- do, the two authorities disagree about the body's arity and the
-- adjustment is a no-op — which reproduces the pre-fix ill-typed
-- emission rather than inventing a signature. That is the intended
-- ordering of bad outcomes (LOUD at Lean over silently plausible),
-- and it is unreached for every contract in the table, where the
-- residual mode count is the SAWCore type's residual arity by
-- construction.
applyAnnotationAdjustment :: AnnotationAdjustment -> Lean.Type -> Lean.Type
applyAnnotationAdjustment adj ty = case adj of
  AnnotateAsIs                    -> ty
  AnnotateWrapped                 -> wrapExcept ty
  AnnotateWrappedArrow adds wrapR
    | spineFits adds ty           -> goArrow wrapR adds ty
    | otherwise                   -> ty
  where
    spineFits [] _ = True
    spineFits (_ : ms) (Lean.Pi (_ : bs) t) =
      spineFits ms (if null bs then t else Lean.Pi bs t)
    spineFits _ _ = False

    goArrow wrapR [] t = if wrapR then wrapExcept t else t
    goArrow wrapR (add : ms) (Lean.Pi (Lean.PiBinder impl nm bty : bs) t) =
      let bty' = if add then wrapExcept bty else bty
          rest = goArrow wrapR ms (if null bs then t else Lean.Pi bs t)
      in case rest of
           Lean.Pi bs' t' -> Lean.Pi (Lean.PiBinder impl nm bty' : bs') t'
           _              -> Lean.Pi [Lean.PiBinder impl nm bty'] rest
    goArrow _ _ t = t
