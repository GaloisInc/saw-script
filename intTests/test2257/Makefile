all: test.linked-mir.json

test.linked-mir.json: test.rs
	saw-rustc test.rs
	$(MAKE) remove-unused-build-artifacts

.PHONY: remove-unused-build-artifacts
remove-unused-build-artifacts:
	rm -f test libtest.mir libtest.rlib

.PHONY: clean
clean: remove-unused-build-artifacts
	rm -f test.linked-mir.json
