all: Makefile.coq mr-solver-tests

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

# If running in GitHub Actions, the $CI environment variable will be defined
# (see https://docs.github.com/en/actions/learn-github-actions/variables#default-environment-variables)
# and these Makefile rules will not be defined. As a consequence, Make will
# /never/ rebuild .bc files. This ensures that the CI will always test the .bc
# files that were checked into version control. (See #1801 for an example of
# what can go wrong if CI rebuilds .bc files with different compilers from what
# were used to originally produce them.)
ifeq ($(CI),)
  %.bc: %.c
	clang -emit-llvm -g -c $<

  xor_swap_rust.bc: xor_swap_rust.rs
	rustc --crate-type=lib --emit=llvm-bc xor_swap_rust.rs

  rust_data.bc: rust_data.rs
	rustc --crate-type=lib --emit=llvm-bc rust_data.rs

  rust_lifetimes.bc: rust_lifetimes.rs
	rustc --crate-type=lib --emit=llvm-bc rust_lifetimes.rs
endif

%_gen.v: %.saw %.bc
	$(SAW) $<

# Lists all the Mr Solver tests, without their ".saw" suffix
MR_SOLVER_TESTS = # arrays_mr_solver linked_list_mr_solver sha512_mr_solver

.PHONY: mr-solver-tests $(MR_SOLVER_TESTS)
mr-solver-tests: $(MR_SOLVER_TESTS)

$(MR_SOLVER_TESTS):
	$(SAW) $@.saw
