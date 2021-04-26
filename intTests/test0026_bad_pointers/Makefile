all: test.ll test.bc

test.ll : test.c
	clang-3.8 -g -O1 -S -emit-llvm test.c
test.bc : test.c
	clang-3.8 -g -O1 -c -emit-llvm test.c
