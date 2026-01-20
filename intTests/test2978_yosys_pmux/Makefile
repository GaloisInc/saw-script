YOSYS?=yosys

all: ex_ite.json ex_case.json

ex_ite.json ex_case.json: ex_ite.v ex_case.v
	$(YOSYS) export.ys

.PHONY: destroy
destroy:
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
