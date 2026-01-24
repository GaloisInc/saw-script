YOSYS?=yosys

all: shift_sshr_unsigned shift_dyn_idx_signed.json shift_dyn_idx.json shift_shl_ext.json shift_shl_trunc.json shift_shr_ext.json shift_shr_trunc.json shift_sshl_ext.json shift_sshl_trunc.json shift_sshr_ext.json shift_sshr_trunc.json

shift_sshr_unsigned shift_dyn_idx_signed.json shift_dyn_idx.json shift_shl_ext.json shift_shl_trunc.json shift_shr_ext.json shift_shr_trunc.json shift_sshl_ext.json shift_sshl_trunc.json shift_sshr_ext.json shift_sshr_trunc.json: test_shift.sv test_shift.ys
	$(YOSYS) -s test_shift.ys

.PHONY: destroy
destroy:
	rm -f *.json

.PHONY: clean
clean:
	@true
