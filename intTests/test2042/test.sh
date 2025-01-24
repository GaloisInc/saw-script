set -e

$SAW test1.saw
! $SAW test2.saw
! $SAW test3.saw

$SAW test4.saw
! $SAW test5.saw
! $SAW test6.saw

