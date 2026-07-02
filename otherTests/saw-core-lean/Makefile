# Local-development driver. The cabal test suite
# `saw-core-lean-tests` invokes `bash test.sh` directly (it sets
# SAW via an `eval saw` env-var so `saw` must be on PATH). For
# local work without a system-wide saw, this Makefile finds the
# binary under dist-newstyle and points the orchestrator at it.

SAW ?= $(shell find $(abspath ../../dist-newstyle) -name saw -type f -perm +111 \
         2>/dev/null | head -1)

export SAW

all test:
	bash test.sh test

conformance:
	bash test.sh conformance

gaps proof-gaps:
	bash test.sh gaps

good:
	bash test.sh good

clean:
	bash test.sh clean

.PHONY: all test conformance gaps proof-gaps good clean
