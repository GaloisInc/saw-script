all: test.ll test.bc

test.ll : test.rs
	rustc --emit=llvm-ir test.rs
test.bc : test.ll
	llvm-as *.bc
