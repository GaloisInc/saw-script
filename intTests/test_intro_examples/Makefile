SAW?=saw
CLANG?=clang
CLANGOPTS?=-c -emit-llvm

CFILES=$(wildcard *.c)
BCFILES=$(patsubst %.c, %.bc, ${CFILES})
LOGFILES=$(patsubst %.saw, %.log, $(wildcard *.saw))

all: deps.mk ${BCFILES}

run: ${LOGFILES}

%.bc: %.c
	${CLANG} ${CLANGOPTS} -o $@ $<

%.log: %.saw
	${SAW} $< 2>&1 | tee $@

clean:
	rm -f ${BCFILES} ${LOGFILES} deps.mk *.cnf

deps.mk: ${CFILES}
	./mkdeps.sh

swap-correct.bc: xor-swap.c direct-swap.c
swap-manual.bc: swap-correct.c xor-swap.c direct-swap.c
swap-random.bc: swap-correct.c xor-swap.c direct-swap.c
-include deps.mk
