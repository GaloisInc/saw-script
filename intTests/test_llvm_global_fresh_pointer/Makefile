CLANG ?= clang
CFLAGS = -g -frecord-command-line

all: test.bc

test.bc: test.c
	$(CLANG) -c -emit-llvm $(CFLAGS) $< -o $@

clean:
	rm -f test.bc

