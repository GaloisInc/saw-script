# The current checked-in linked-mir.json file was generated by:
#    rustc 1.69.0-nightly (5e37043d6 2023-01-22)
#    mir-json c52b16bf26af2f5b98157ebf9975aa0021982bbc from 2024-09-11

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
