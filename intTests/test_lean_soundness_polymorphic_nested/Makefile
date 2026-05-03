SAW ?= $(shell find ../../dist-newstyle -name saw -type f -perm +111 \
         2>/dev/null | head -1)

ifeq ($(SAW),)
$(error No saw binary found under dist-newstyle. \
        Run `cabal build exe:saw` first or pass SAW=/path/to/saw)
endif

export SAW

test:
	bash test.sh

run-tests:
	bash test.sh run-tests

show:
	bash test.sh show-diffs

good:
	bash test.sh good

clean:
	bash test.sh clean

.PHONY: test run-tests show good clean
