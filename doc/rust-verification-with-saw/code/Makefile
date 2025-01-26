RS_FILES   := $(wildcard *.rs)
JSON_FILES := $(RS_FILES:.rs=.linked-mir.json)
EXE_FILES  := $(RS_FILES:.rs=)

all: $(JSON_FILES)

%.linked-mir.json: %.rs
	saw-rustc $<
	$(MAKE) remove-unused-build-artifacts

.PHONY: remove-unused-build-artifacts
remove-unused-build-artifacts:
	rm -f test lib*.mir lib*.rlib $(EXE_FILES)

.PHONY: clean
clean: remove-unused-build-artifacts
	rm -f *.linked-mir.json
