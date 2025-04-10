#!/bin/sh
set -e

mkdir -p tmp
cp ../../doc/llvm-java-verification-with-saw/code/* tmp
cd tmp
$SAW des-cryptol2.saw
$SAW des3.saw
$SAW dotprod.saw
$SAW double.saw
cd ..
rm -r tmp
