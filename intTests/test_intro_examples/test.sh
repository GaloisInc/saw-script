#!/bin/sh
set -e

$SAW ffs_bug.saw
$SAW ffs_bug_fail.saw
$SAW ffs_eq.saw
! $SAW ffs_extract.saw
$SAW ffs_sat.saw
$SAW rewrite.saw
$SAW swap-simpler.saw
! $SAW swap.saw
$SAW swap_extract.saw
$SAW unfold.saw
! $SAW unint.saw
$SAW write_cnf.saw
