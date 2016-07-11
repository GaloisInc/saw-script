
all:
	clang -std=c99 -O2 -DWITH_TESTS -o chacha20.exe chacha20.c
	clang -std=c99 -c -emit-llvm -o chacha20.bc chacha20.c
	saw chacha20.saw
clean:
	rm -f *.bc *~ *.exe
