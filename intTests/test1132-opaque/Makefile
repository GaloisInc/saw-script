# NB: Ensure that clang-15 or later is used so that the resulting LLVM bitcode
# uses opaque pointers.
CC = clang
CFLAGS = -g -emit-llvm -frecord-command-line -O0

all: test.bc

test.bc: test.c
	$(CC) $(CFLAGS) -c $< -o $@

.PHONY: clean
clean:
	rm -f test.bc
