set -e

$SAW test.saw
abc -c "cec java_md5.aig md5_ref.aig" | grep "Networks are equivalent."
rm -f *.aig
