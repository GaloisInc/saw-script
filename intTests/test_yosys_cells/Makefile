# Split tests into $NFILES equally-sized "test.n.saw" test files.
NFILES = 6

SAW ?= saw
CABAL ?= cabal
YOSYS ?= yosys

SAW_FILES = $(foreach n,$(shell seq 1 $(NFILES)), test.$(n).saw)

.PHONY: run
run: $(SAW_FILES) test.json test.sh
	bash test.sh

# Parses Yosys truth-table output to generate Cryptol specs for each module.
# Add "--non-fatal" arg to "cabal run" to see all failures.
$(SAW_FILES): test.log YosysSpecs.hs yosys-cell-tests.cabal
	$(CABAL) run yosys-specs -- -n $(NFILES) <$<

# Run the generated Yosys script to evaluate each module, generating
# truth-tables.
test.log: test.ys test.json
	$(YOSYS) <$< >$@
	grep -vzq ERROR $@

# Generate Yosys JSON RTLIL output for evaluation by Yosys and SAW. To change
# the set of cells instantiated and tested (at various parameter values),
# modify the definition of "tests" in instantiate_cells.hs.
.PRECIOUS: test.json
test.json test.ys: InstantiateCells.hs yosys-cell-tests.cabal
	$(CABAL) run instantiate-cells test.json test.ys

.PHONY: clean
clean:
	rm -f test.ys test.log
	$(CABAL) clean

.PHONY: purge
purge: clean
	rm -f test.json $(SAW_FILES)
