.PHONY: run clean

run: source.bc
	../../bin/saw partial-spec.saw

clean:
	rm -f *.bc *.ll

%.bc: %.c
	clang -O0 -g -emit-llvm -c -o $@ $^

%.ll: %.c
	clang -O0 -g -emit-llvm -c -S -o $@ $^
