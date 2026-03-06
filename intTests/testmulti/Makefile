bld: all main

LLVM_C_SRCS=foo bar main
CFLAGS=-g
include ../support/llvm-blobs.mk

main: main.bc foo.bc bar.bc
	clang -o $@ $^
