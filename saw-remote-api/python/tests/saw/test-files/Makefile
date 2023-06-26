C_FILES    := $(wildcard *.c)
BC_FILES   := $(C_FILES:.c=.bc)
RS_FILES   := $(wildcard *.rs)
JSON_FILES := $(RS_FILES:.rs=.linked-mir.json)

all: $(BC_FILES) $(JSON_FILES)

%.bc: %.c
	clang -g -c -emit-llvm -o $@ $<

%.linked-mir.json: %.rs
	saw-rustc $<

# This test case crucially relies on the use of -O2.
llvm_lax_pointer_ordering.bc: llvm_lax_pointer_ordering.c
	clang -O2 -g -c -emit-llvm -o $@ $<
