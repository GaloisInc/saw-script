# Make Emacs-format tags.
.PHONY: tmp/TAGS
tmp/TAGS: | tmp
	hasktags --ignore-close-implementation --etags --tags-absolute --output=tmp/TAGS src deps/*/src

tmp:
	mkdir -p tmp

# saw-core-lean comprehensive validation — the single CI gate.
#
# Required for ANY change touching the Lean backend (translator,
# support library, soundness lockdowns, drivers, proofs, etc.).
# Exits non-zero on the first failure.
#
# Coverage:
#   (1) Tests       — Haskell-side translator invariants
#                     (L-1..L-17 lockdowns) via the smoketest.
#   (2) Synthesis   — SAW emission for every driver in
#                     otherTests/saw-core-lean/drivers/ and
#                     saw-boundary/, diffed against pinned .good.
#   (3) Proofs      — Lean discharges every goal in
#                     otherTests/saw-core-lean/proofs/, including
#                     llvm_verify-emitted obligations.
#   (4) Assurance   — Hand-rolled negative-attack probes pinning
#                     axiom signatures (shape/), and the
#                     CryptolToLean Lean support library compiles.
#   (5) SAW broad   — General SAW integration tests (intTests/) to
#                     catch regressions in non-Lean SAW
#                     infrastructure that could affect the Lean
#                     backend transitively (e.g. Cryptol parser,
#                     scNormalize, Crucible).
.PHONY: test-saw-core-lean
test-saw-core-lean:
	@echo "=== 1/5: build SAW with current translator ==="
	cabal build exe:saw
	@echo "=== 2/5: build CryptolToLean support library ==="
	( cd saw-core-lean/lean && lake build )
	@echo "=== 3/5: Haskell-side translator invariants (smoketest) ==="
	cabal test saw-core-lean-smoketest
	@echo "=== 4/5: Lean-side driver/proof/shape/saw-boundary ==="
	cabal test saw-core-lean-tests
	@echo "=== 5/5: SAW general integration tests ==="
	cabal test integration-tests
	@echo
	@echo "=== ALL SAW-CORE-LEAN VALIDATIONS PASSED ==="

# saw-core-lean focused semantic conformance gate.
#
# This is intentionally namespaced rather than a generic `conformance`
# target: it is a SAW-Lean backend suite, not a whole-repository
# conformance statement.
.PHONY: test-saw-core-lean-conformance
test-saw-core-lean-conformance:
	@echo "=== build SAW with current translator ==="
	cabal build exe:saw
	@echo "=== saw-core-lean differential conformance ==="
	$(MAKE) -C otherTests/saw-core-lean conformance
