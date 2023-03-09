set -e

# This test case uses `write_aiger` to produce AIG files for two nearly
# identical functions, where the only difference is the order of arguments (one
# symbolic and one concrete) in a bitvector multiplication. If the `aig` library
# does its job correctly, these should produce identical AIG files, so check
# this using `diff`.
$SAW test.saw
diff -ru left.aig right.aig
