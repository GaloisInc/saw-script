C_FILES  := $(wildcard *.c)
BC_FILES := $(C_FILES:.c=.bc)

all: $(BC_FILES)

%.bc: %.c
	clang -g -c -emit-llvm -o $@ $<

# This test case crucially relies on the use of -O2.
llvm_lax_pointer_ordering.bc: llvm_lax_pointer_ordering.c
	clang -O2 -g -c -emit-llvm -o $@ $<
