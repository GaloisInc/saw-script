{-# LANGUAGE OverloadedStrings #-}

{- |
Module      : SAWCoreLean.FixShapes
Copyright   : Galois, Inc. 2026
License     : BSD3
Maintainer  : saw@galois.com
Stability   : experimental
Portability : portable

Phase 5 — recognizer for `Prelude.fix` shapes that the Lean backend
can soundly lower without introducing partial-recursion machinery.

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
  -- conservatism of "produces a Stream" is enough for Slice A. The
  -- mutual-stream @PairType (Stream A) (Stream A)@ shape is a
  -- separate match for Slice A.5.
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
  | otherwise = NotMatched
      "shape not recognized for Lean lowering (StreamCorec / \
      \PairStreamCorec are the matched shapes; others fall through \
      \to the L-5 reject path)"
