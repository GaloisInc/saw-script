CC = clang
CFLAGS = -g -O0

all: foo.bc

foo.bc: foo.c
	$(CC) $(CFLAGS) -c -emit-llvm $< -o $@

.PHONY: clean
clean:
	rm -f foo.bc
