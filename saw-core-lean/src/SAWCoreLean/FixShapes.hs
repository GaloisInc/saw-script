{-# LANGUAGE OverloadedStrings #-}

{- |
Module      : SAWCoreLean.FixShapes
Copyright   : Galois, Inc. 2026
License     : BSD3
Maintainer  : saw@galois.com
Stability   : experimental
Portability : portable

Recognizer for `Prelude.fix` shapes that the Lean backend can
soundly lower without introducing partial-recursion machinery.

The design rationale lives in
@saw-core-lean/doc/2026-05-02_recursion-design.md@. In short: SAWCore
@Prelude.fix@ rejected wholesale (the L-5 lockdown) is too coarse
when Cryptol's productivity guarantee makes some shapes
uniquely-determined and reachable via plain Lean structural
recursion. The recognizer here matches those shapes; everything
else continues to fall through to L-5.

Soundness rests on two residual-trust assumptions documented in
@doc/2026-05-XX_residual-trust.md@: Cryptol enforces productivity at
the source level, and @scNormalizeForLean@ preserves it. Under those,
each shape we recognize denotes a unique fixed point that the
corresponding Lean lowering computes structurally.
-}

module SAWCoreLean.FixShapes
  ( FixShape(..)
  , classifyFix
  , classifyPolyStreamIterate
  ) where

import           Data.Text             (Text)

import           SAWCore.Recognizer
import           SAWCore.SharedTerm    (Term)

-- | A SAWCore @Prelude.fix typeArg bodyArg@ application matched to
-- one of the shapes the Lean backend can soundly lower. 'NotMatched'
-- is the fall-through used to decide between routing to a shape-
-- specific lowering and the L-5 reject path.
data FixShape
  = StreamCorec
      { scElType :: Term
        -- ^ The element type @α@ in @Stream α@.
      , scBody   :: Term
        -- ^ The full body @\\rec -> MkStream α (\\i -> e[rec, i])@.
        --   Translated by the lowering pass; the lookup-form
        --   substitution happens at Lean-AST level by applying the
        --   translated body to @Stream.MkStream lookup@.
      }
  | PairStreamCorec
      { pscElTypeA :: Term
        -- ^ Element type of the first stream.
      , pscElTypeB :: Term
        -- ^ Element type of the second stream.
      , pscBody    :: Term
        -- ^ The full body
        --   @\\x -> PairValue1 _ _ (MkStream α f1) (MkStream β f2)@
        --   where @f1@/@f2@ access the recursive @x@ via
        --   @Stream#rec@ over @PairType1#rec1@ projections.
        --   Translated by the lowering pass.
      }
  | BoundedVecFold
      { bvfLen    :: Term
        -- ^ The vector length term @n@ (kept as a SAWCore term so
        --   the lowering can translate it; will typically be a
        --   literal but addNat/etc. are also possible).
      , bvfElType :: Term
        -- ^ The element type @α@ in @Vec n α@.
      , bvfBody   :: Term
        -- ^ The full body @\\rec -> gen n α (\\i -> e[rec, i])@.
        --   Translated by the lowering pass; the lookup-form
        --   substitution at Lean-AST level applies the translated
        --   body to @gen n α lookup@ and projects the i-th element
        --   via @atWithDefault@.
      }
  | NotMatched Text
    -- ^ Diagnostic explaining why the recognizer didn't fire. The
    --   caller surfaces this to the user via the existing L-5
    --   'RejectedPrimitive' channel.
  deriving (Show)

-- | Classify a @Prelude.fix@ application after the head and arguments
-- have been split. The arity-2 contract (@fix typeArg bodyArg@) is
-- assumed; callers should verify @length args == 2@ before calling.
classifyFix :: Term -> Term -> FixShape
classifyFix typeArg bodyArg
  -- Single-stream shape: @fix (Stream α) (\\rec -> MkStream α (\\i -> e))@.
  --
  --   * @typeArg@ must be a @Prelude.Stream@ application yielding
  --     the element type.
  --   * @bodyArg@ must be a lambda whose body is a @Prelude.MkStream@
  --     application — i.e. the recursion produces a stream rather
  --     than e.g. consuming one.
  --
  -- Tighter checks (every @rec@ usage goes through a @Stream#rec@
  -- access at a syntactically-earlier index) are deferred — the
  -- end-to-end semantic test is the strongest pin, and the
  -- conservatism of "produces a Stream" is enough. The mutual-stream
  -- @PairType (Stream A) (Stream B)@ shape is matched separately
  -- below.
  | Just [elType] <- asGlobalApply "Prelude.Stream" typeArg
  , Just (_recName, _recTy, recBody) <- asLambda bodyArg
  , Just _mkStreamArgs <- asGlobalApply "Prelude.MkStream" recBody
  = StreamCorec
      { scElType = elType
      , scBody   = bodyArg
      }
  -- Mutual-stream shape:
  --   fix (PairType1 (Stream α) (Stream β))
  --       (\\x -> PairValue1 _ _ (MkStream α f1) (MkStream β f2))
  --
  --   * @typeArg@ is @PairType1 (Stream α) (Stream β)@ (both type
  --     args must themselves be @Stream@ applications).
  --   * @bodyArg@ is a lambda whose body is a @PairValue1@
  --     application; the two value args are @MkStream α _@ and
  --     @MkStream β _@.
  | Just [pairAType, pairBType] <- asGlobalApply "Prelude.PairType1" typeArg
  , Just [elTypeA] <- asGlobalApply "Prelude.Stream" pairAType
  , Just [elTypeB] <- asGlobalApply "Prelude.Stream" pairBType
  , Just (_xName, _xTy, recBody) <- asLambda bodyArg
  , Just pairValArgs <- asGlobalApply "Prelude.PairValue1" recBody
  , [_pairAType', _pairBType', mkStreamA, mkStreamB] <- pairValArgs
  , Just _ <- asGlobalApply "Prelude.MkStream" mkStreamA
  , Just _ <- asGlobalApply "Prelude.MkStream" mkStreamB
  = PairStreamCorec
      { pscElTypeA = elTypeA
      , pscElTypeB = elTypeB
      , pscBody    = bodyArg
      }
  -- Bounded Vec fold:
  --   fix (Vec n α) (\\rec -> gen n α (\\i -> e[rec, i]))
  --
  -- The earlier blocker for this shape was our own `zip` axiom,
  -- which had the wrong return type (`PairType a b` flat, but SAW's
  -- `#(a, b)` syntax expands to `PairType a (PairType b UnitType)`
  -- per `saw-core/src/SAWCore/Typechecker.hs:414-418`). The axiom
  -- now matches SAW's actual nested-with-Unit form.
  | Just [vecLen, elType] <- asGlobalApply "Prelude.Vec" typeArg
  , Just (_recName, _recTy, recBody) <- asLambda bodyArg
  , Just _genArgs <- asGlobalApply "Prelude.gen" recBody
  = BoundedVecFold
      { bvfLen    = vecLen
      , bvfElType = elType
      , bvfBody   = bodyArg
      }
  | otherwise = NotMatched
      "shape not recognized for Lean lowering (StreamCorec, \
      \PairStreamCorec, BoundedVecFold are the matched shapes; \
      \others fall through to the L-5 reject path)"

-- | Classify a polymorphic stream-iteration @Prelude.fix@ application
-- — the shape Cryptol's @iterate : { a } (a -> a) -> a -> [inf]a@
-- lowers to.
--
-- The full SAWCore application is @fix typeArg bodyArg α_arg f_arg x_arg@
-- (i.e. @Prelude.fix@ with /five/ args, not the usual two — the extra
-- three monomorphise the polymorphism). The recognizer pattern-matches:
--
--   * @typeArg = Pi (a : sort 0) (Pi (a -> a) (Pi a (Stream a)))@
--     (a 3-binder Pi spine ending in @Stream@ applied to the first
--     binder)
--   * @bodyArg = \\rec -> \\a -> \\f -> \\x -> MkStream a (\\i -> ...)@
--     (a 4-deep outer-lambda chain ending in @MkStream@)
--
-- Returns the three extra args when matched: @α_arg@ (the type),
-- @f_arg@ (the step function), @x_arg@ (the seed). The lowering site
-- emits a @cryptolIterate α_arg f_arg x_arg@ call to the hand-written
-- structural-recursion def in
-- @CryptolToLean.SAWCorePreludeExtra.cryptolIterate@.
--
-- Returns 'Nothing' if any of the structural checks fail; caller falls
-- through to the existing 'classifyFix' / L-5 reject path.
classifyPolyStreamIterate :: Term -> Term -> [Term] -> Maybe (Term, Term, Term)
classifyPolyStreamIterate typeArg bodyArg extras
  -- Three extras: α, f, x.
  | [alphaArg, fArg, xArg] <- extras
  -- typeArg has 3 Pi binders ending in `Stream <first-binder>`.
  , (piBinders, retTy) <- asPiList typeArg
  , length piBinders == 3
  , Just [_streamElTy] <- asGlobalApply "Prelude.Stream" retTy
  -- bodyArg has 4 outer lambdas ending in MkStream.
  , (lamBinders, innerBody) <- asLambdaList bodyArg
  , length lamBinders == 4
  , Just (_:_) <- asGlobalApply "Prelude.MkStream" innerBody
  = Just (alphaArg, fArg, xArg)
  | otherwise = Nothing
