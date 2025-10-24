set -e

$SAW present01.saw < present01.stdin
$SAW present02.saw < present02.stdin

$SAW leak01.saw < leak01.stdin
$SAW leak02.saw < leak02.stdin
$SAW leak03.saw < leak03.stdin
$SAW leak04.saw < leak04.stdin
$SAW leak05.saw < leak05.stdin
