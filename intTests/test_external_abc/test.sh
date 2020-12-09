set -e

SCRIPT="%blast; &sweep -C 5000; &syn4; &cec -m"

$SAW test.saw

abc -q "%read offline_verilog.prove0.v; $SCRIPT" | grep "are equivalent"
abc -q "%read write_verilog_unsat.v; $SCRIPT" | grep "are equivalent"
abc -q "%read write_verilog_sat.v; $SCRIPT" | grep "are NOT EQUIVALENT"

z3 w4_offline_smtlib2.prove0.smt2 | grep "^unsat$"
z3 write_smtlib2_w4_sat.smt2 | grep "^sat$"
z3 write_smtlib2_w4_unsat.smt2 | grep "^unsat$"
