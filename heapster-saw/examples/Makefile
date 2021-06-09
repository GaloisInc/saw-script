all: Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

include Makefile.coq

SAW=cabal run saw

%.bc: %.c
	clang -emit-llvm -g -c $<

linked_list.v: linked_list.bc linked_list.saw linked_list.sawcore
	$(SAW) linked_list.saw

xor_swap.v: xor_swap.bc xor_swap.saw
	$(SAW) xor_swap.saw

xor_swap_rust.bc: xor_swap_rust.rs
	rustc --crate-type=lib --emit=llvm-bc xor_swap_rust.rs

xor_swap_rust.v: xor_swap_rust.bc xor_swap_rust.saw
	$(SAW) xor_swap_rust.saw

string_set.v: string_set.bc string_set.saw string_set.sawcore
	$(SAW) string_set.saw

loops.v: loops.bc loops.saw loops.sawcore
	$(SAW) loops.saw

arrays.v: arrays.bc arrays.saw arrays.sawcore
	$(SAW) arrays.saw

iter_linked_list.v: iter_linked_list.bc iter_linked_list.saw iter_linked_list.sawcore
	$(SAW) iter_linked_list.saw

iso_recursive.v: iso_recursive.bc iso_recursive.saw iso_recursive.sawcore
	$(SAW) iso_recursive.saw

memcpy.v: memcpy.bc memcpy.saw memcpy.sawcore
	$(SAW) memcpy.saw

rust_data.bc: rust_data.rs
	rustc --crate-type=lib --emit=llvm-bc rust_data.rs

rust_data.v: rust_data.bc rust_data.saw
	$(SAW) rust_data.saw

rust_lifetimes.bc: rust_lifetimes.rs
	rustc --crate-type=lib --emit=llvm-bc rust_lifetimes.rs

rust_lifetimes.v: rust_lifetimes.bc rust_lifetimes.saw
	$(SAW) rust_lifetimes.saw
