CC = clang
CFLAGS = -g -emit-llvm -frecord-command-line -O1

all: test.bc

test.bc: test.c
	$(CC) $(CFLAGS) -c $< -o $@

.PHONY: clean
clean:
	rm -f test.bc
