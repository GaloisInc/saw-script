CC = clang
CFLAGS = -g -frecord-command-line -O0

all: test.bc

test.bc: test.c
	$(CC) $(CFLAGS) -c -emit-llvm $< -o $@

.PHONY: clean
clean:
	rm -f test.bc
