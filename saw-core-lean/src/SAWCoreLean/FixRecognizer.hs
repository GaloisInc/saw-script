{-# LANGUAGE OverloadedStrings #-}

{- |
Module      : SAWCoreLean.FixRecognizer
Copyright   : Galois, Inc. 2026
License     : BSD3
Maintainer  : saw@galois.com
Stability   : experimental
Portability : portable

The OP-3 successor productivity recognizer for wrapped @Prelude.fix@
applications: pure, SOURCE-side classification only (never inspects
emitted Lean — calculus rule). Extracted from "SAWCoreLean.Term" in
the 2026-07-17 module split; the recognizer SURFACE IS FROZEN after
Slice R3b — any growth requires the fragment reference semantics
program first (doc/2026-07-16_fragment-semantics-scoping.md). The
lowerings that consume these verdicts (@lowerClassFBounded@,
@lowerClassSSingle@, @lowerFixProofObligation@) live in
"SAWCoreLean.Term".
-}

module SAWCoreLean.FixRecognizer
  ( FixClass(..)
  , classifyFixShape
  , fixVerdictReason
  , asSingletonArraySeed
  , termHeadName
  , termSpine
  , traceFixClass
  ) where

import qualified Data.IntSet                  as IntSet
import           Data.Foldable                (toList)
import           Data.Either                  (lefts, rights)
import           Data.Maybe                   (isJust)
import qualified Debug.Trace
import           System.Environment           (lookupEnv)
import           System.IO.Unsafe             (unsafePerformIO)

import           SAWCore.Name
import           SAWCore.Recognizer
import           SAWCore.Term.Functor
import           SAWCore.Term.Raw             (Term(..), freeVars, unwrapTermF)

-- | OP-3 Slice R0 (doc/2026-07-15_op3-successor-design.md, slice
-- plan): the productivity recognizer, INERT — classification + trace
-- only. NOTHING in emission may branch on the result until Slice R2
-- flips the Class-F gate (and Slice R3 the stream gates); until then
-- this is the migration's differential oracle, mirroring the Slice-0
-- 'SAW_LEAN_TRACE_POSITIONS' pattern.
data FixClass
  = FixClassF
    -- ^ Finite bounded-lookback (Class F): @Vec n α@-typed fix whose
    -- body is @\rec -> append [seed] (gen k (\i -> elt))@ with seed
    -- length exactly 1 (amendment B) and every recursive reference
    -- consumed through the zip/at family at the append's constant
    -- @-1@ shift (amendment C; the per-instance semantic guarantee
    -- is Slice R2's PROVEN @H_prod@ obligation, not this syntactic
    -- gate — amendment A).
  | FixClassSSingle
    -- ^ Stream single-step corecursion (Class S): @Stream α@-typed
    -- fix in MkStream-headed or single-step append form.
  | FixClassSPaired
    -- ^ Mutual paired-stream fix (@PairType (Stream _) (Stream _)@).
    -- Amendment D: OWN disposition — Slice R3 rejects it with a named
    -- diagnostic; a paired lowering is a separate later design.
  | FixUnrecognized String
    -- ^ Everything else, with the reason the gate will name when
    -- Slice R2 activates rejection.
  deriving (Eq, Show)

-- | The reason string a rejection carries for an unrecognized (or
-- position-mismatched) wrapped fix verdict.
fixVerdictReason :: FixClass -> String
fixVerdictReason (FixUnrecognized r) = r
fixVerdictReason FixClassF =
  "Class F recognized at a non-wrapped position"
fixVerdictReason FixClassSSingle =
  "Class S-single recognized at a non-wrapped position"
fixVerdictReason FixClassSPaired =
  "paired-stream fix (rejected upstream)"

-- | Classify a wrapped @Prelude.fix@ application from its SOURCE-side
-- type and body terms — never from emitted Lean (calculus rule). The
-- checks are deliberately narrow and syntactic; when in doubt the
-- verdict is 'FixUnrecognized' (reject-when-gated, never guess).
classifyFixShape :: Term -> Term -> FixClass
classifyFixShape typeArg bodyArg
    -- the prelude has both the sort-0 PairType and the sort-1
    -- PairType1 spelling; paired-stream fixes arrive at the latter
  | Just [sa, sb] <- asAnyPairType typeArg
  , isStreamType sa && isStreamType sb
  = FixClassSPaired
  | isStreamType typeArg
  = classifyStreamBody
  | Just [_n, _a] <- asGlobalApply "Prelude.Vec" typeArg
  = classifyVecBody
  | otherwise
  = FixUnrecognized
      ("fix at a type outside Vec/Stream/paired-Stream: "
       ++ termHeadName typeArg)
  where
    isStreamType t = isJust (asGlobalApply "Prelude.Stream" t)

    asAnyPairType t = case asGlobalApply "Prelude.PairType" t of
      Just as -> Just as
      Nothing -> asGlobalApply "Prelude.PairType1" t

    -- Class S-single (R3a hardening): a bare MkStream head is NOT
    -- enough to gate an emission flip. The corpus's canonical
    -- single-step shape (rec_ones) is
    --   \rec -> MkStream a (\i -> atWithDefault 1 a
    --                        <Stream.rec read of rec, using its
    --                         index function only at (subNat i 1)>
    --                        <rec-free literal seed of length 1> i)
    -- Element 0 comes from the seed; element i reads the recursive
    -- stream only at i-1. Anything looser stays Unrecognized until a
    -- lowering for it is designed.
    classifyStreamBody = case asLambda bodyArg of
      Nothing -> FixUnrecognized "stream fix body is not a lambda"
      Just (recVn, _recTy, inner) ->
        case asGlobalApply "Prelude.MkStream" inner of
          Just [_elemTy, idxF] -> case asLambda idxF of
            Just (iVn, _ity, fbody) ->
              classifyStreamElem recVn iVn fbody
            Nothing ->
              FixUnrecognized "MkStream index function is not a lambda"
          _ ->
            FixUnrecognized
              ("stream fix body head is not MkStream: "
               ++ termHeadName inner)

    classifyStreamElem recVn iVn fbody =
      case asGlobalApply "Prelude.atWithDefault" fbody of
        Just [sLen, _elemTy, dflt, seedV, idx]
          | asNat sLen /= Just 1 ->
              FixUnrecognized "stream seed length is not the literal 1"
          | not (isExactVar iVn idx) ->
              FixUnrecognized
                "stream atWithDefault index is not the MkStream binder"
          | termMentionsVar recVn seedV ->
              FixUnrecognized
                "recursive binder occurs in the stream seed"
          -- R3b review finding F1: the gate must equal the lowering's
          -- destructure exactly — the lowering extracts x0 from a
          -- literal single-element ArrayValue, so a computed
          -- length-1 seed (gen 1 …, a bound vector) must classify
          -- Unrecognized here, not surface as an internal-invariant
          -- error downstream. Reject-when-unsure direction.
          | Nothing <- asSingletonArraySeed seedV ->
              FixUnrecognized
                "stream seed is not a literal single-element vector"
          | otherwise -> classifyStreamTail recVn iVn dflt
        _ ->
          FixUnrecognized
            ("stream element body is not the seeded atWithDefault "
             ++ "form: " ++ termHeadName fbody)

    -- The recursor value (recursor + params + motive + elims) is
    -- applied to the scrutinee as an ordinary App; 'asRecursorApp'
    -- recognizes only the former (Stream has no indices), so peel
    -- the scrutinee first.
    classifyStreamTail recVn iVn dflt
      | Just (recFn, scrut) <- asApp dflt
      , Just (crec, _params, motive, [caseFn], []) <-
          asRecursorApp recFn
      , ModuleIdentifier dtIdent <- nameInfo (recursorDataType crec)
      , identName dtIdent == "Stream"
      = if not (isExactVar recVn scrut)
          then FixUnrecognized
            "stream read scrutinee is not the recursive binder"
        else if termMentionsVar recVn motive
          then FixUnrecognized
            "recursive binder occurs in the stream read motive"
        else if termMentionsVar recVn caseFn
          then FixUnrecognized
            "recursive binder occurs outside the scrutinee \
            \of the stream read"
        else case asLambda caseFn of
          Just (sVn, _sty, caseBody) ->
            -- R3 audit amendment 1 (2026-07-15, load-bearing): the
            -- case body must be EXACTLY the identity read
            -- @s (subNat i 1)@. A wrapping transformation
            -- (@f (s (i-1))@ — the iterate family) is raw at the
            -- SAWCore layer this recognizer sees, but its Lean
            -- translation may be Except-valued (checked indexing,
            -- division, …), and the only validated R3 lowering is
            -- the identity step. Accepting more would make the
            -- gate broader than the sound lowering — the
            -- structural draft's failure mode. The iterate
            -- generalization is the post-R4 program.
            if isIdentityStreamRead iVn sVn caseBody
              then FixClassSSingle
              else FixUnrecognized
                "stream step is not the identity read \
                \(iterate-family transformations are not realized)"
          Nothing ->
            FixUnrecognized "stream case function is not a lambda"
      | otherwise =
          FixUnrecognized
            ("stream tail is not a Stream.rec read of the "
             ++ "recursive stream: " ++ termHeadName dflt)

    -- @caseBody@ must be the bare application of the stream index
    -- function binder to the constant -1 shift of the MkStream
    -- binder — nothing above it, nothing around it.
    isIdentityStreamRead iVn sVn caseBody
      | Just (fh, arg) <- asApp caseBody
      , Just (vn, _) <- asVariable fh
      , vnIndex vn == vnIndex sVn
      = isShiftMinusOne iVn arg
      | otherwise = False

    -- The corpus's normalized Class-F form is the FUSED gen/ite shape
    -- (scNormalizeForLean folds the Cryptol append into one gen):
    --   \rec -> gen N a (\i -> ite a (ltNat i 1)
    --                              <seed branch, rec-free>
    --                              (at K a (gen K a (\i2 -> elt))
    --                                  (subNat i 1)))
    -- The constant -1 shift (amendment C) lives at the tail branch:
    -- result[i] = innerGen[i-1], and inside elt the recursive binder
    -- is read through zip at the INNER binder exactly — so
    -- result[i] reads rec only at index i-1 < i.
    classifyVecBody = case asLambda bodyArg of
      Nothing -> FixUnrecognized "vec fix body is not a lambda"
      Just (recVn, _recTy, inner) ->
        case asGlobalApply "Prelude.gen" inner of
          Just [_nTot, _elemTy, genF] -> case asLambda genF of
            Just (iVn, _ityp, iteBody) ->
              classifyFusedIte recVn iVn iteBody
            Nothing -> FixUnrecognized "gen element function is not a lambda"
          _ ->
            FixUnrecognized
              ("vec fix body head is not the fused gen form: "
               ++ termHeadName inner)

    classifyFusedIte recVn iVn iteBody =
      case asGlobalApply "Prelude.ite" iteBody of
        Just [_a, cond, seedBranch, tailBranch]
          | not (isSeedGuard iVn cond) ->
              FixUnrecognized
                ("element guard is not (ltNat i 1): " ++ termSpine 2 cond)
          | termMentionsVar recVn cond ->
              FixUnrecognized "recursive binder occurs in the element guard"
          | termMentionsVar recVn seedBranch ->
              FixUnrecognized "recursive binder occurs in the seed branch"
          | otherwise -> classifyTail recVn iVn tailBranch
        _ ->
          FixUnrecognized
            ("gen element body is not an ite: " ++ termHeadName iteBody)

    classifyTail recVn iVn tailBranch =
      case asGlobalApply "Prelude.at" tailBranch of
        Just [_k, _pty, vec, idx]
          | not (isShiftMinusOne iVn idx) ->
              FixUnrecognized
                ("tail selection index is not the constant -1 shift: "
                 ++ termSpine 2 idx)
          | otherwise -> case asGlobalApply "Prelude.gen" vec of
              Just [_k2, _a2, innerF] -> case asLambda innerF of
                Just (i2Vn, _t2, elt) -> recUseVerdict recVn i2Vn elt
                Nothing ->
                  FixUnrecognized "inner gen element function is not a lambda"
              _ ->
                FixUnrecognized
                  ("shifted tail is not an inner gen: " ++ termHeadName vec)
        _ ->
          FixUnrecognized
            ("tail branch is not an at-selection: "
             ++ termHeadName tailBranch)

    isSeedGuard iVn cond =
      case asGlobalApply "Prelude.ltNat" cond of
        Just [iv, bound]
          | Just (vn, _) <- asVariable iv
          , vnIndex vn == vnIndex iVn
          , asNat bound == Just 1 -> True
        _ -> False

    -- Amendment-C discipline, syntactic side: every occurrence of the
    -- recursive binder inside the element function must sit inside a
    -- zip application (the corpus's parallel-comprehension form), and
    -- every at-selection whose vector spine CONTAINS the recursive
    -- binder must be indexed by the constant -1 shift of the outer
    -- gen binder (@subNat i 1@) — a same-index or computed-index body
    -- must NOT classify (it would be unsound to lower, third/fourth
    -- audits).
    recUseVerdict recVn idxVn elt =
      case scanRecUses recVn idxVn False elt of
        Left reason -> FixUnrecognized reason
        Right sawRecUse
          | sawRecUse -> FixClassF
          | otherwise ->
              FixUnrecognized
                "no recursive reference under the append arm (not a recurrence)"

    -- Walk the element term. Returns Left reason on a forbidden use,
    -- Right sawAnyUse otherwise. 'inZip' tracks whether we are inside
    -- a zip argument slot (the only place a BARE rec reference is
    -- permitted).
    scanRecUses recVn idxVn = go
      where
        go inZip t
          | Just (vn, _) <- asVariable t =
              if vnIndex vn == vnIndex recVn
                then if inZip
                       then Right True
                       else Left "recursive binder used outside a zip slot"
                else Right False
          | Just [_a, _b, _m, _k, xs, ys] <- asGlobalApply "Prelude.zip" t =
              -- Sixth-audit Finding 0 (2026-07-16): a zip OPERAND
              -- admits exactly the bare recursive vector — nothing
              -- wrapped around it. Blessing the whole operand spine
              -- (the previous `go True`) admitted index-permuting or
              -- forcing-opaque wrappers one level down
              -- (@zip … (reverse rec) xs@, @zip … (bvAnd rec m) xs@),
              -- the same class the at-spine rule already rejects.
              -- Any non-bare operand is scanned with the zip
              -- blessing OFF, so a deeper rec must re-qualify
              -- through the at/zip rules on its own.
              combine [goZipSlot xs, goZipSlot ys]
          | Just [_n, _pty, vec, idx] <- asGlobalApply "Prelude.at" t
          , termMentionsVar recVn vec =
              -- inside the inner gen the -1 shift has already been
              -- applied at the tail branch, so a rec-containing
              -- at-selection must be indexed by EXACTLY the inner
              -- binder — any further index arithmetic is out of the
              -- recognized class. The selected spine must be the
              -- recursive vector itself or reach it through zip
              -- slots only (scanned with inZip=False, so the zip
              -- rule is the sole admitter): an index-permuting
              -- wrapper like @reverse rec@ would silently break the
              -- lookback direction if the whole spine were blessed.
              if isExactVar idxVn idx
                then if isExactVar recVn vec
                       then Right True
                       else go False vec
                else Left "rec-containing at-selection index is not the inner gen binder"
          | otherwise =
              case toList (unwrapTermF t) of
                [] -> Right False
                cs -> combine (map (go inZip) cs)

        combine rs = case lefts rs of
          (e : _) -> Left e
          [] -> Right (or (rights rs))

        goZipSlot t
          | Just (vn, _) <- asVariable t
          , vnIndex vn == vnIndex recVn = Right True
          | otherwise = go False t

    termMentionsVar vn t = vnIndex vn `IntSet.member` freeVars t

    isExactVar vn t = case asVariable t of
      Just (vn', _) -> vnIndex vn' == vnIndex vn
      Nothing -> False

    isShiftMinusOne idxVn idx =
      case asGlobalApply "Prelude.subNat" idx of
        Just [base, one]
          | Just (vn, _) <- asVariable base
          , vnIndex vn == vnIndex idxVn
          , asNat one == Just 1 -> True
        _ -> False

-- | The one seed shape the Class S-single lowering can consume: a
-- literal ArrayValue with exactly one element. This is the SHARED
-- spelling of the seed guard — 'classifyStreamElem' (the gate) and
-- 'lowerClassSSingle' (the lowering) both go through it, so the two
-- can never drift apart on it again (R3b review finding F1).
asSingletonArraySeed :: Term -> Maybe Term
asSingletonArraySeed t = case asArrayValue t of
  Just (_ty, [elt]) -> Just elt
  _ -> Nothing

termHeadName :: Term -> String
termHeadName t = case asGlobalDef (fst (asApplyAll t)) of
  Just i  -> identName i
  Nothing -> case unwrapTermF t of
    Lambda {}   -> "lam"
    Variable {} -> "var"
    tf          -> take 24 (show tf)

-- | Depth-limited application-spine dump for the R0 trace: head name
-- plus argument heads, recursively. Debug instrumentation only.
termSpine :: Int -> Term -> String
termSpine d t
  | d <= 0 = termHeadName t
  | Just (_vn, _ty, body) <- asLambda t =
      "(lam. " ++ termSpine (d - 1) body ++ ")"
  | otherwise =
      case asApplyAll t of
        (_, []) -> termHeadName t
        (h, as) ->
          "(" ++ termHeadName h ++ " "
              ++ unwords (map (termSpine (d - 1)) as) ++ ")"

-- | One-shot read of @SAW_LEAN_TRACE_FIX_CLASS@, mirroring
-- 'positionTraceEnabled'. Debug instrumentation only; nothing
-- downstream may depend on it.
fixClassTraceEnabled :: Bool
fixClassTraceEnabled =
  unsafePerformIO (isJust <$> lookupEnv "SAW_LEAN_TRACE_FIX_CLASS")
{-# NOINLINE fixClassTraceEnabled #-}

traceFixClass :: Monad m => Term -> Term -> m ()
traceFixClass typeArg bodyArg
  | not fixClassTraceEnabled = pure ()
  | otherwise =
      Debug.Trace.traceM $
        "[fixClass] type=" ++ termHeadName typeArg
        ++ " verdict=" ++ show (classifyFixShape typeArg bodyArg)
        ++ " spine=" ++ termSpine 8 bodyArg

