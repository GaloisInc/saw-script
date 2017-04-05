#!/bin/sh
set -e

mkdir -p tmp
cp -r ../../examples/ecdsa/* tmp
cd tmp
SAW=${SAW} make verify
cd ..
rm -r tmp
