# Convenience wrapper around test.sh so the common workflow
# `make test` / `make good` / `make clean` doesn't require chasing the
# SAW binary path manually. The cabal test runner ignores this file
# entirely — it dispatches `bash test.sh` directly per
# intTests/IntegrationTest.hs.

# Locate the saw binary built by `cabal build exe:saw`. Override on
# the command line when you've installed saw elsewhere:
#   make SAW=/path/to/saw test
SAW ?= $(shell find ../../dist-newstyle -name saw -type f -perm +111 \
         2>/dev/null | head -1)

ifeq ($(SAW),)
$(error No saw binary found under dist-newstyle. \
        Run `cabal build exe:saw` first or pass SAW=/path/to/saw)
endif

export SAW

# `make test` — run the test, fail loudly on diffs.
test:
	bash test.sh

# `make run-tests` — run without checking diffs (useful when
# triaging by hand). `make show` prints whatever diffs accumulated.
run-tests:
	bash test.sh run-tests

show:
	bash test.sh show-diffs

# `make good` — accept the current outputs as the new reference.
# Use only when the diff is intentional.
good:
	bash test.sh good

# `make clean` — wipe all generated files.
clean:
	bash test.sh clean

.PHONY: test run-tests show good clean
