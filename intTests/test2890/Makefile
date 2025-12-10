GHDL?=ghdl
YOSYS?=yosys

all: test.json

test.json: test.vhd
	$(GHDL) -a $<
	$(YOSYS) -p 'ghdl add4; flatten; write_json -compat-int test.json'
	$(MAKE) tidy

.PHONY: tidy
tidy:
	rm -f *.o work-obj93.cf

.PHONY: destroy
destroy: tidy
	rm -f *.json

# "clean" does nothing here; just make sure it exists.
# "clean" is for removing test run results, and we don't
# incur any just by having test blobs.
#
# Unfortunately, it looks like we need a dummy rule with an invocation
# of true to keep gmake from getting upset.
.PHONY: clean
clean:
	@true
