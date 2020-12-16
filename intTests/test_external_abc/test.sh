set -e

CEX=_tmp_cex
SCRIPT="%blast; &sweep -C 5000; &syn4; &cec -m; write_aiger_cex $CEX"

rm -f ${CEX}

$SAW test.saw

abc -q "%read offline_verilog.prove0.v; $SCRIPT" || true;
[ ! -f ${CEX} ]
abc -q "%read write_verilog_unsat.v; $SCRIPT" || true;
[ ! -f ${CEX} ]
abc -q "%read write_verilog_sat.v; $SCRIPT" || true;
[ -s ${CEX} ]

z3 w4_offline_smtlib2.prove0.smt2 | grep "^unsat$"
z3 write_smtlib2_w4_sat.smt2 | grep "^sat$"
z3 write_smtlib2_w4_unsat.smt2 | grep "^unsat$"

rm -f ${CEX}
