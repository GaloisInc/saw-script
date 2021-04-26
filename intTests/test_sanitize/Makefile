all: add-normal.bc add-sanitized.bc

%-normal.bc: %.c
	clang -c  -emit-llvm -o $@ $<

%-sanitized.bc: %.c
	clang -c -fsanitize=unsigned-integer-overflow -fsanitize-trap=unsigned-integer-overflow -emit-llvm -o $@ $<

clean:
	rm -f *.bc
