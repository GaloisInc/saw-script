all: unsound_global.linked-mir.json

unsound_global.linked-mir.json: unsound_global.rs
	saw-rustc $<
	$(MAKE) remove-unused-build-artifacts

.PHONY: remove-unused-build-artifacts
remove-unused-build-artifacts:
	rm -f unsound_global libunsound_global.mir libunsound_global.rlib

.PHONY: clean
clean: remove-unused-build-artifacts
	rm -f unsound_global.linked-mir.json
