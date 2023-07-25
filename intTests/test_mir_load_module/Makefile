all: test.json

test.linked-mir.json: test.rs
	saw-rustc $<

.PHONY: clean
clean:
	rm -f test.linked-mir.json
