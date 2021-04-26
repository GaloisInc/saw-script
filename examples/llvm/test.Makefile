# Generic makefile for simple LLVM tests consisting of three files:
# 'test.c', 'test.cry', and 'test.saw'.
#
# Used by the 'iterative_average' and 'union'.

all: tmp/test.bc tmp/test.ll tmp/test

tmp/test.bc: test.c
	mkdir -p tmp
	clang -c -emit-llvm $< -o tmp/test.o
	llvm-link tmp/test.o -o $@

tmp/test.ll: tmp/test.bc
	llvm-dis -o $@ $<

tmp/test: tmp/test.bc
	llvm-link -o $@ $<
	chmod +x $@

.PHONY: clean
clean:
	-rm -rf tmp
