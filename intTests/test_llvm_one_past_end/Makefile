CLANG ?= clang

test.bc: test.c
	$(CLANG) -c -emit-llvm -g -o $@ $^
