all : test1.bc test2.bc

test1.bc : test1.c
	clang -c -emit-llvm -g -o test1.bc test1.c

test2.bc : test2.c
	clang -c -emit-llvm -g -o test2.bc test2.c
