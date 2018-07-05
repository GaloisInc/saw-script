#!/bin/sh
set -e

mkdir -p tmp
cp ../../doc/tutorial/code/* tmp
cd tmp
sed -i.bak s/abc/w4/g ffs_java.saw
sed -i.bak s/abc/w4/g ffs_llvm.saw
sed -i.bak s/abc/w4/g ffs_compare.saw
sed -i.bak s/abc/w4/g ffs_gen_aig.saw
sed -i.bak s/abc/w4/g ffs_compare_aig.saw
sed -i.bak s/abc/w4/g java_add.saw
sed -i.bak s/abc/w4/g nqueens.saw
$SAW ffs_java.saw
$SAW ffs_llvm.saw
# $SAW ffs_compare.saw
$SAW ffs_gen_aig.saw
$SAW ffs_compare_aig.saw
$SAW java_add.saw
$SAW nqueens.saw
cd ..
# rm -r tmp
