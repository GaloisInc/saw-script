C_FILES  := $(wildcard *.c)
BC_FILES := $(C_FILES:.c=.bc)

all: $(BC_FILES)

%.bc: %.c
	clang -g -c -emit-llvm -o $@ $<
