all: Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

include Makefile.coq

# If running in CI, always set $SAW=`which saw`. Otherwise, if saw is not in the
# current path, fall back on cabal run saw
SAW=$(shell which saw)
ifeq ($(SAW),)
  ifeq ($(CI),)
	    SAW=cabal run saw
  else
    $(error Could not find SAW executable; PATH = $(PATH))
  endif
endif

ifeq ($(CI),)
  %.bc: %.c
	clang -emit-llvm -g -c $<
endif

%_gen.v: %.saw %.bc
	$(SAW) $<

xor_swap_rust.bc: xor_swap_rust.rs
	rustc --crate-type=lib --emit=llvm-bc xor_swap_rust.rs

rust_data.bc: rust_data.rs
	rustc --crate-type=lib --emit=llvm-bc rust_data.rs

rust_lifetimes.bc: rust_lifetimes.rs
	rustc --crate-type=lib --emit=llvm-bc rust_lifetimes.rs
