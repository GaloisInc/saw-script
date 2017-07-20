.PHONY: run clean

run: source.bc
	../../bin/saw fresh-post.saw

clean:
	rm -f *.bc *.ll

%.bc: %.c
	clang -O0 -emit-llvm -c -o $@ $^

%.ll: %.c
	clang -O0 -emit-llvm -c -S -o $@ $^
