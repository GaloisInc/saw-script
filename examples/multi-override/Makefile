.PHONY: run clean

run: source.bc
	../../bin/saw multi-override.saw

clean:
	rm -f *.bc *.ll

%.bc: %.c
	clang -O0 -emit-llvm -g -c -o $@ $^

%.ll: %.c
	clang -O0 -emit-llvm -g -c -S -o $@ $^
