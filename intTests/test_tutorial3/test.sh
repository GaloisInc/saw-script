#!/bin/sh
set -e

mkdir -p tmp
cp ../../doc/llvm-java-verification-with-saw/code/* tmp
cd tmp
$SAW nqueens.saw
cd ..
rm -r tmp
