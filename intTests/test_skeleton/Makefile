bld: all main

LLVM_C_SRCS=foo bar
CFLAGS=-g
include ../support/llvm-blobs.mk

main: foo.bc bar.bc
	llvm-link -o test.bc foo.bc bar.bc

clean:
	rm skel_{builtins|direct}

