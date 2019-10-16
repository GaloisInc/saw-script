.PHONY: all test clean

CC ?= clang
CFLAGS ?= -O0 -emit-llvm
SAW ?= saw

C_FILES = $(wildcard *.c)
BC_FILES = $(C_FILES:.c=.bc)
LL_FILES = $(BC_FILES:.bc=.ll)
SAW_FILES = $(wildcard *.saw)

all: $(BC_FILES) $(LL_FILES) test

test: $(BC_FILES)
	$(SAW) $(SAW_FILES)

clean:
	rm -f *.bc *.ll *.log

%.bc: %.c
	$(CC) $(CFLAGS) -c -o $@ $^

%.ll: %.c
	$(CC) $(CFLAGS) -c -S -o $@ $^
