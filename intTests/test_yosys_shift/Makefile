YOSYS?=yosys

all: shift_dyn_idx.json shift_dyn_idx_signed.json

shift_dyn_idx.json shift_dyn_idx_signed.json: test_shift.sv test_shift.ys
	$(YOSYS) -s test_shift.ys

.PHONY: destroy
destroy:
	rm -f *.json

.PHONY: clean
clean:
	@true
