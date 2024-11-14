CC = clang
CFLAGS = -g -frecord-command-line -O0

all: test.bc test.exe

test.bc: test.c
	$(CC) $(CFLAGS) -c -emit-llvm $< -o $@

test.o: test.c
	$(CC) $(CFLAGS) -c $< -o $@

test.exe: test.o
	$(CC) $(CFLAGS) $< -o $@

.PHONY: clean
clean:
	rm -f test.bc test.exe
