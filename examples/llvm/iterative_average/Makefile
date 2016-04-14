all: tmp/test.bc tmp/test

tmp/test.bc: test.c
	mkdir -p tmp
	clang -c -emit-llvm $< -o tmp/test.o
	llvm-link tmp/test.o -o $@

tmp/test: tmp/test.bc
	llvm-link -o $@ $<
	chmod +x $@

.PHONY: clean
clean:
	-rm -rf tmp
