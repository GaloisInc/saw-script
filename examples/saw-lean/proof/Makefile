# Discharges for the two `offline_lean` properties in
# ../demo.saw. We derive LEAN_PATH from `lake env` so the support
# library and toolchain are picked up portably (no hard-coded
# /Users/... paths). `lake build` must have run in
# saw-core-lean/lean/ at least once for the support library's
# .olean to be on disk.

LAKE_DIR  := $(shell cd ../../../saw-core-lean/lean && pwd)
HERE      := $(shell pwd)
BASE_PATH := $(shell cd $(LAKE_DIR) && lake env env | sed -n 's/^LEAN_PATH=//p')

.PHONY: invol eq clean

invol:
	LEAN_PATH=$(BASE_PATH) lean -o $(HERE)/invol/Emitted.olean $(HERE)/invol/Emitted.lean
	LEAN_PATH=$(HERE)/invol:$(BASE_PATH) lean $(HERE)/invol/proof.lean

eq:
	LEAN_PATH=$(BASE_PATH) lean -o $(HERE)/eq/Emitted.olean $(HERE)/eq/Emitted.lean
	LEAN_PATH=$(HERE)/eq:$(BASE_PATH) lean $(HERE)/eq/proof.lean

clean:
	rm -f invol/Emitted.olean invol/Emitted.ilean eq/Emitted.olean eq/Emitted.ilean
