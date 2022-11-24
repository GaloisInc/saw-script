%.bc : %.c
	clang -g -O1 -c -emit-llvm $< -o $@

clean:
	rm -rf *.o *.bc
