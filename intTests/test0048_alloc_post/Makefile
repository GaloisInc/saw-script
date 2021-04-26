all: test.ll test.bc test

CC = clang
CFLAGS = -g -O0

test : test.c
	$(CC) $(CFLAGS) -o test test.c
test.ll : test.c
	$(CC) $(CFLAGS) -S -emit-llvm test.c
test.bc : test.c
	$(CC) $(CFLAGS) -c -emit-llvm test.c
