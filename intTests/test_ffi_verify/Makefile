test.bc: test.c
	clang -Wall -Werror -g -c -emit-llvm $< -o $@

.PHONY: clean
clean:
	rm test.bc
