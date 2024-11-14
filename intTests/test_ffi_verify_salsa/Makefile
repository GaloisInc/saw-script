salsa.bc: salsa.c ecrypt-*.h
	clang -Wall -Werror -g -c -emit-llvm $< -o $@

.PHONY: clean
clean:
	rm salsa.bc
