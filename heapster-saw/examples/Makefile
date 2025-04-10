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

  dilithium: dilithium.patch
	rm -rf dilithium
	git clone https://github.com/pq-crystals/dilithium.git
	# NB: If you update this commit hash be sure to also update the commit hash
	#     in the top-level comment in `heapster-saw/examples/Dilithium2.saw`
	cd dilithium && git checkout 918af1a6eaedcedf9fdd8aaaca6c1fccd5a7a51f
	patch -p0 < dilithium.patch

  # NB: So far we've only been able to get this step to work on a Ubuntu VM,
  # so building dilithium2.bc, etc. locally on a non-Ubuntu machine is likely
  # not possible without significant effort to configure clang appropriately
  dilithium%.bc: dilithium
	cd dilithium/ref && LLVM_COMPILER=clang make bitcode
	cp dilithium/ref/libpqcrystals_dilithium$*_ref.so.bc dilithium$*.bc
endif

%_gen.v: %.saw %.bc
	$(SAW) $<

# Lists all the Mr Solver tests without their ".saw" suffix, except Dilithium2
# FIXME: Get linked_list and sha512 working with type descriptions
MR_SOLVER_TESTS = higher_order_mr_solver exp_explosion_mr_solver \
                  arrays_mr_solver # linked_list_mr_solver sha512_mr_solver

.PHONY: mr-solver-tests $(MR_SOLVER_TESTS) Dilithium2
mr-solver-tests: $(MR_SOLVER_TESTS) Dilithium2

$(MR_SOLVER_TESTS):
	$(SAW) $@.saw

Dilithium2: dilithium2.bc
	$(SAW) Dilithium2.saw
