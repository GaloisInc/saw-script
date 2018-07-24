.PHONY: run clean

run: source.bc
	../../bin/saw fresh-post-good.saw
	../../bin/saw fresh-post-bad.saw

clean:
	rm -f *.bc *.ll

%.bc: %.c
	clang -O0 -emit-llvm -c -o $@ $^

%.ll: %.c
	clang -O0 -emit-llvm -c -S -o $@ $^
