YOSYS?=yosys

all: test.json

test.json: test.sv test.ys
	$(YOSYS) -s test.ys

.PHONY: destroy
destroy:
	rm -f *.json

.PHONY: clean
clean:
	@true
