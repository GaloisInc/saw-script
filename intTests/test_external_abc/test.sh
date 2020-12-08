set -e

SCRIPT="%blast; &sweep -C 5000; &syn4; &cec -m"

$SAW test.saw

abc -q "%read offline_verilog.prove0.v; $SCRIPT" | grep "are equivalent"
abc -q "%read write_verilog_unsat.v; $SCRIPT" | grep "are equivalent"
abc -q "%read write_verilog_sat.v; $SCRIPT" | grep "are NOT EQUIVALENT"
