#!/usr/bin/env sh

set -e
mkdir -p tmp

$SAW test0.saw
$SAW test1.saw

rm -rf tmp
