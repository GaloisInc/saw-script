.PHONY: run clean

run: simple.bc
	../../bin/saw ghost.saw

clean:
	rm -f *.bc *.ll

%.bc: %.c
	clang -O0 -emit-llvm -c -o $@ $^

%.ll: %.c
	clang -O0 -emit-llvm -c -S -o $@ $^
