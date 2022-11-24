.SUFFIXES: .c .bc

%.bc : %.c
	clang -g -O0 -c -emit-llvm $< -o $@
