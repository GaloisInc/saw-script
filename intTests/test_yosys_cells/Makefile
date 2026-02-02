SAW ?= saw
CABAL ?= cabal
YOSYS ?= yosys

.PHONY: run
run: test.saw test.json
	$(SAW) $<

# Parses Yosys truth-table output to generate Cryptol specs for each module.
# Add "-- --non-fatal" arg to "cabal run" to see all failures.
test.saw: test.log yosys_specs.hs
	$(CABAL) run yosys_specs.hs <$< >$@

# Run the generated Yosys script to evaluate each module, generating
# truth-tables.
test.log: test.json test.ys
	$(YOSYS) <test.ys >$@
	grep -vzq ERROR $@

# Generate Yosys JSON RTLIL output for evaluation by Yosys and SAW. To change
# the set of cells instantiated and tested (at various parameter values),
# modify the definition of "tests" in instantiate_cells.hs.
.PRECIOUS: test.json
test.json test.ys &: instantiate_cells.hs
	$(CABAL) run $< $@ test.ys

.PHONY: clean
clean:
	rm -f test.ys test.log

.PHONY: purge
purge: clean
	rm -f test.json test.saw
