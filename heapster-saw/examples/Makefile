all: Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

include Makefile.coq

# If the saw executable is available, use it, otherwise fall back on cabal run saw
SAW=$(shell which saw || echo cabal run saw)

%.bc: %.c
	clang -emit-llvm -g -c $<

%_gen.v: %.saw %.bc
	$(SAW) $<

xor_swap_rust.bc: xor_swap_rust.rs
	rustc --crate-type=lib --emit=llvm-bc xor_swap_rust.rs

rust_data.bc: rust_data.rs
	rustc --crate-type=lib --emit=llvm-bc rust_data.rs

rust_lifetimes.bc: rust_lifetimes.rs
	rustc --crate-type=lib --emit=llvm-bc rust_lifetimes.rs
