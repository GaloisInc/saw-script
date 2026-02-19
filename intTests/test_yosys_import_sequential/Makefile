YOSYS?=yosys

all: kclmul.json kclmulr.json

kclmul.json jclmulr.json: kclmul.sv kclmulr.sv test.ys
	$(YOSYS) -s test.ys

.PHONY: destroy
destroy:
	rm -f *.json

.PHONY: clean
clean:
	@true
