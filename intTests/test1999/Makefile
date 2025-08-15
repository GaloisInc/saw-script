all: post-test post-test-mut pre-test pre-test-mut clean-mir-json

post-test: post-test.rs
	saw-rustc $<

post-test-mut: post-test-mut.rs
	saw-rustc $<

pre-test: pre-test.rs
	saw-rustc $<

pre-test-mut: pre-test-mut.rs
	saw-rustc $<

clean-mir-json:
	rm -f *.rlib *.mir pre-test pre-test-mut post-test post-test-mut

# Removes everything including mir-json output and linked MIR JSON
clean-all: clean-mir-json
	rm -f *.linked-mir.json
