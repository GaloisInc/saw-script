#!/usr/bin/env bash
# Generate a chacha20-core qround proofs/ row from its emitted golden
# and the quarterround's four state positions. Produced the eight
# landed rows proofs/llvm_chacha20_core_qround_{c0..c3,d0..d3}
# (2026-07-22); rerun after an emission change regenerates a row from
# the refreshed .lean.good in one command.
# Usage: gen-qround-row.sh <rowname> <obligation-stem> <p0> <p1> <p2> <p3>
#   e.g. gen-qround-row.sh llvm_chacha20_core_qround_c0 \
#          qround_c0_LLVM_points-to0 0 4 8 12
set -eu

SAW_ROOT="$(cd "$(dirname "$0")/../../.." && pwd)"
WF=otherTests/saw-core-lean/workflows/llvm_chacha20_core_verify
ROWS=$SAW_ROOT/otherTests/saw-core-lean/proofs

name="$1"; stem="$2"; p0="$3"; p1="$4"; p2="$5"; p3="$6"
golden="$SAW_ROOT/$WF/test_llvm_chacha20_core_verify.${stem}.lean.good"
row="$ROWS/$name"
mkdir -p "$row"

# Header
cat > "$row/completed.lean" <<EOF
/-
ChaCha20 core-round quarterround verify (obligation ${stem},
state positions ${p0},${p1},${p2},${p3}) — completed outline, ACCEPTED
under the \`native-eval\` trust tier (2026-07-21 user decision; see
.trust-tier).

One of the EIGHT qround obligations emitted by
workflows/llvm_chacha20_core_verify (four column rounds, four diagonal
rounds); same quarterround equation as proofs/llvm_chacha20_q_eq at a
different position tuple. The generated \`def goal\` embeds vacuous
bounds-proof fallbacks whose dead admit-placeholder tails are stripped
here (proof irrelevance keeps \`goal\` rfl-equal to the generated
goal; the harness drift check enforces that), and \`goal_holds\` is
discharged: rowround-recipe scaffold with the rotate bridge at the
ChaCha20 rotation amounts {16,12,8,7}; the 12 unchanged positions
close by bvEq_refl, the 4 quarterround positions by \`bv_decide\`.

TRUST TIER NOTE — RESOLVE LATER: \`bv_decide\` proofs depend on
per-invocation proof-local native axioms
(\`goal_holds._native.bv_decide.ax_*\`); see the two-tier policy in
saw-core-lean/doc/proof-cookbook.md. RESOLUTION TRIGGER (recorded in
TODO.md): when lean-smt's cvc5 BV proof reconstruction lands upstream,
swap \`bv_decide\` -> \`smt\` and delete .trust-tier.
-/
EOF

# Emitted content, dead fallback tails stripped, goal_holds stub dropped.
stub_line=$(grep -n '^theorem goal_holds' "$golden" | cut -d: -f1)
sed 's/| skip); all_goals sorry));/| skip)));/' "$golden" \
    | head -n $((stub_line - 1)) >> "$row/completed.lean"

# Lemma library + discharge.
cat >> "$row/completed.lean" <<'EOF'
open CryptolToLean.SAWCorePrimitives CryptolToLean.SAWCoreVectors
  CryptolToLean.SAWCoreBitvectorsProofs CryptolToLean.SAWCorePreludeProofs

/-- The IN-ITP override at rotate granularity: the C shift-or
    decomposition of a 32-bit left-rotate equals the Cryptol `rotateL`.
    Same bridge as the salsa20 rowround/columnround rows, at the
    ChaCha20 rotation amounts. -/
theorem rotl_shlor_32 (x : Vec 32 Bool) (k : Nat) (hk : k < 32) :
    bvOr 32 (bvShl 32 x k) (bvShr 32 x (32 - k)) = rotateL 32 Bool x k := by
  have h : vecToBitVec (bvOr 32 (bvShl 32 x k) (bvShr 32 x (32 - k)))
         = vecToBitVec (rotateL 32 Bool x k) := by
    rw [vecToBitVec_bvOr, vecToBitVec_bvShl, vecToBitVec_bvShr, vecToBitVec_rotateL,
        BitVec.rotateLeft_def, Nat.mod_eq_of_lt hk]
  calc bvOr 32 (bvShl 32 x k) (bvShr 32 x (32 - k))
      = bitVecToVec (vecToBitVec (bvOr 32 (bvShl 32 x k) (bvShr 32 x (32-k)))) :=
        (bitVecToVec_vecToBitVec _).symm
    _ = bitVecToVec (vecToBitVec (rotateL 32 Bool x k)) := by rw [h]
    _ = rotateL 32 Bool x k := bitVecToVec_vecToBitVec _

theorem rotl_16 (x : Vec 32 Bool) : bvOr 32 (bvShl 32 x 16) (bvShr 32 x 16) = rotateL 32 Bool x 16 := rotl_shlor_32 x 16 (by decide)
theorem rotl_12 (x : Vec 32 Bool) : bvOr 32 (bvShl 32 x 12) (bvShr 32 x 20) = rotateL 32 Bool x 12 := rotl_shlor_32 x 12 (by decide)
theorem rotl_8  (x : Vec 32 Bool) : bvOr 32 (bvShl 32 x 8)  (bvShr 32 x 24) = rotateL 32 Bool x 8  := rotl_shlor_32 x 8  (by decide)
theorem rotl_7  (x : Vec 32 Bool) : bvOr 32 (bvShl 32 x 7)  (bvShr 32 x 25) = rotateL 32 Bool x 7  := rotl_shlor_32 x 7  (by decide)

/-- Abstract eager-sequence reduction: a literal vector of successes
    sequences to the pure vector. Proved once over opaque elements so
    the main discharge applies it as a single rewrite to the huge
    emitted words (not by inline monadic peeling). -/
theorem vecSeqM_map_ok {α n} (w : Vec n α) :
    vecSequenceM n α (Vector.map Except.ok w) = Except.ok w := by
  apply vecSequenceM_ok_of_get; intro i; simp

theorem seq4 (e0 e1 e2 e3 : Vec 32 Bool) :
    vecSequenceM 4 (Vec 32 Bool) #v[Except.ok e0, Except.ok e1, Except.ok e2, Except.ok e3] = Except.ok #v[e0, e1, e2, e3] := by
  rw [show (#v[Except.ok e0, Except.ok e1, Except.ok e2, Except.ok e3] : Vec 4 (Except String (Vec 32 Bool)))
        = Vector.map Except.ok #v[e0, e1, e2, e3] from by simp, vecSeqM_map_ok]

theorem seq16 (e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 : Vec 32 Bool) :
    vecSequenceM 16 (Vec 32 Bool) #v[Except.ok e0, Except.ok e1, Except.ok e2, Except.ok e3, Except.ok e4, Except.ok e5, Except.ok e6, Except.ok e7, Except.ok e8, Except.ok e9, Except.ok e10, Except.ok e11, Except.ok e12, Except.ok e13, Except.ok e14, Except.ok e15] = Except.ok #v[e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15] := by
  rw [show (#v[Except.ok e0, Except.ok e1, Except.ok e2, Except.ok e3, Except.ok e4, Except.ok e5, Except.ok e6, Except.ok e7, Except.ok e8, Except.ok e9, Except.ok e10, Except.ok e11, Except.ok e12, Except.ok e13, Except.ok e14, Except.ok e15] : Vec 16 (Except String (Vec 32 Bool)))
        = Vector.map Except.ok #v[e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15] from by simp, vecSeqM_map_ok]

theorem foldr_ofFn_true (n : Nat) :
    Vector.foldr (fun a acc => Bool.rec (Except.ok (ε := String) false) acc a) (Except.ok true)
      (Vector.ofFn (fun _ : Fin n => true)) = Except.ok true := by
  induction n with
  | zero => rfl
  | succ k ih =>
    have hsplit : (Vector.ofFn (fun _ : Fin (k+1) => true))
                = (Vector.ofFn (fun _ : Fin k => true)).push true := by
      apply Vector.ext; intro i hi
      simp only [Vector.getElem_ofFn]
      by_cases hk : i < k
      · simp [Vector.getElem_push_lt hk]
      · have : i = k := by omega
        subst this; simp
    rw [hsplit, Vector.foldr_push]; exact ih

theorem foldr_ofFn_all_true {n : Nat} (g : Fin n → Bool) (h : ∀ i, g i = true) :
    Vector.foldr (fun a acc => Bool.rec (Except.ok (ε := String) false) acc a) (Except.ok true)
      (Vector.ofFn g) = Except.ok true := by
  have hg : Vector.ofFn g = Vector.ofFn (fun _ : Fin n => true) := by
    apply Vector.ext; intro i hi; simp only [Vector.getElem_ofFn]; exact h ⟨i, hi⟩
  rw [hg, foldr_ofFn_true]

set_option maxRecDepth 100000 in
theorem goal_holds : goal := by
  intro state
  simp only [goal, Pure.pure, Bind.bind, Except.pure, Except.bind,
    natPos_macro, bit0_macro, bit1_macro, one_macro, zero_macro,
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub,
    seq4, seq16, atWithProof_checkedM, genWithBoundsM,
    rotl_16, rotl_12, rotl_8, rotl_7,
    foldrM, ofFnM_except_ok, bvEq_refl, CryptolToLean.SAWCorePreludeExtra.iteM,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero]
  apply foldr_ofFn_all_true
  simp only [Fin.forall_fin_succ, Fin.forall_fin_zero, and_true]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
EOF

# Per-position closes: bv_decide at the quarterround tuple, bvEq_refl
# passthrough elsewhere.
for i in $(seq 0 15); do
    if [ "$i" = "$p0" ] || [ "$i" = "$p1" ] || [ "$i" = "$p2" ] || [ "$i" = "$p3" ]; then
        cat >> "$row/completed.lean" <<'EOF'
  · simp only [Fin.val_zero, Fin.val_succ, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_succ, List.getElem_cons_zero]
    unfold bvEq
    refine decide_eq_true ?_
    simp only [vecToBitVec_bvXor, vecToBitVec_bvAdd, vecToBitVec_rotateL]
    bv_decide
EOF
    else
        cat >> "$row/completed.lean" <<'EOF'
  · simp only [Fin.val_zero, Fin.val_succ, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_succ, List.getElem_cons_zero]
    exact bvEq_refl _ _
EOF
    fi
done

printf '%s/test_llvm_chacha20_core_verify.%s.lean\n' "$WF" "$stem" > "$row/source.txt"

cat > "$row/proof.lean" <<'EOF'
/-
ChaCha20 core-round quarterround verify — native-eval trust tier row
(see completed.lean header and .trust-tier). goal_holds carries the
discharge; the four qround equations close by bv_decide.
-/

import Emitted

theorem goal_closed : goal :=
  goal_holds
EOF

cat > "$row/.trust-tier" <<'EOF'
# Non-strict trust tier for this row (2026-07-21 user decision):
# bv_decide closes the four qround equations; its per-invocation
# proof-local native axioms are admitted for THIS ROW ONLY.
# RESOLVE LATER: swap bv_decide -> smt and delete this file when
# lean-smt BV proof reconstruction lands upstream.
native-eval
EOF

echo "generated $row"
