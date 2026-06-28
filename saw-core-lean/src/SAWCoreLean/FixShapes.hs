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
  ) where

import qualified Data.Text             as Text
import           Data.Text             (Text)

import           SAWCore.Name          (VarName, nameInfo, toAbsoluteName,
                                        vnName)
import           SAWCore.Recognizer
import           SAWCore.SharedTerm    (Term)
import           SAWCore.Term.Functor  (CompiledRecursor(..),
                                        FlatTermF(..), TermF(..))
import           SAWCore.Term.Raw      (unwrapTermF)

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
      , bvfRecName :: VarName
        -- ^ Recursive vector binder in the body lambda. The selected-element
        --   lowering binds this name to @Pure.pure (gen n α lookup)@ while
        --   translating the element generator.
      , bvfBody   :: Term
        -- ^ The full body @\\rec -> gen n α (\\i -> e[rec, i])@.
        --   Translated by the lowering pass as the literal vector body.
      , bvfElemBody :: Term
        -- ^ The element generator from the @gen@ body. The lowering emits this
        --   as the selected-element view and asks Lean to prove it agrees with
        --   the literal vector body.
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
  -- This recognizer checks only the outer shape needed to select a
  -- lowering. It is not, by itself, a productivity proof: semantic
  -- soundness also needs the documented invariant that recursive
  -- lookups at index @i@ demand only already-computed indices. Today
  -- that invariant is residual trust inherited from Cryptol and
  -- @scNormalizeForLean@; a backend contract that accepts arbitrary
  -- SAWCore @fix@ terms needs a separate local productivity gate before
  -- reaching this lowering. The mutual-stream @PairType (Stream A)
  -- (Stream B)@ shape is matched separately below.
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
  , Just (recName, _recTy, recBody) <- asLambda bodyArg
  , Just [_genLen, _genElType, elemBody] <- asGlobalApply "Prelude.gen" recBody
  = BoundedVecFold
      { bvfLen    = vecLen
      , bvfElType = elType
      , bvfRecName = recName
      , bvfBody   = bodyArg
      , bvfElemBody = elemBody
      }
  | otherwise = NotMatched (fixShapeMissReason typeArg bodyArg)

fixShapeMissReason :: Term -> Term -> Text
fixShapeMissReason typeArg bodyArg =
  Text.intercalate "; " . filter (not . Text.null) $
    [ "type argument head: " <> termHeadSummary typeArg
    , "type argument Pi binders: " <> countText (length typeBinders)
    , "type argument return head: " <> termHeadSummary typeRet
    , appArgsSummary "type argument app arg heads" typeArg
    , "body lambda binders: " <> countText (length bodyBinders)
    , "body return head: " <> termHeadSummary bodyRet
    , appArgsSummary "body return app arg heads" bodyRet
    , "matched shapes: StreamCorec, PairStreamCorec, and BoundedVecFold"
    ]
  where
    (typeBinders, typeRet) = asPiList typeArg
    (bodyBinders, bodyRet) = asLambdaList bodyArg

countText :: Int -> Text
countText = Text.pack . show

termHeadSummary :: Term -> Text
termHeadSummary tm =
  let (headTerm, args) = asApplyAll tm
      arity = length args
      withArity headText
        | arity == 0 = headText
        | otherwise =
            headText <> " applied to " <> countText arity <> " argument(s)"
  in case asGlobalDef headTerm of
       Just ident ->
         withArity ("constant " <> Text.pack (show ident))
       Nothing ->
         withArity (termNodeSummary headTerm)

appArgsSummary :: Text -> Term -> Text
appArgsSummary label tm =
  case snd (asApplyAll tm) of
    [] -> ""
    args ->
      label <> ": [" <> Text.intercalate ", " (map termHeadSummary args) <> "]"

termNodeSummary :: Term -> Text
termNodeSummary tm =
  case unwrapTermF tm of
    FTermF (Recursor rec) ->
      "recursor for " <> toAbsoluteName (nameInfo (recursorDataType rec))
    FTermF (Sort s _) ->
      "sort " <> Text.pack (show s)
    FTermF (ArrayValue _ xs) ->
      "array literal of length " <> countText (length xs)
    FTermF (StringLit _) ->
      "string literal"
    App{} ->
      "application"
    Lambda{} ->
      "lambda"
    Pi{} ->
      "Pi"
    Constant nm ->
      "constant " <> toAbsoluteName (nameInfo nm)
    Variable vn _ ->
      "variable " <> vnName vn
