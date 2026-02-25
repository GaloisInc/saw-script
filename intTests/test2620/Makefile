RLIBS ?= $(HOME)/mir-json/rlibs
SAW_RUSTC ?= saw-rustc

.PHONY: run
run: test.linked-mir.json test.sh
	./test.sh

test.linked-mir.json: test.rs
	SAW_RUST_LIBRARY_PATH=$(RLIBS) $(SAW_RUSTC) $<

.PHONY: clean
clean:
	rm -f libtest.mir libtest.rlib test.linked-mir.json
