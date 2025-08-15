# The current checked-in artifacts were generated using the following tools:
#    rustc 1.86.0-nightly (9cd60bd2c 2025-02-15)
#    mir-json ae8c20d96b874ee977b5fba0f02059d6593943a8 from 2025-08-06
#
# Notes: This format may be sensitive to changes in mir-json schema versions.

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
