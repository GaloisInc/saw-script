all : vectortest.ll vectortest.bc vectortest

vectortest.ll : vectortest.c
	clang-3.8 -S -emit-llvm -O1 -g -mpclmul vectortest.c
vectortest.bc : vectortest.c
	clang-3.8 -c -emit-llvm -O1 -g -mpclmul vectortest.c
vectortest : vectortest.c
	clang-3.8 -o vectortest -O1 -g -mpclmul vectortest.c
