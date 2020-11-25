#!/bin/sh
set -e

mkdir -p tmp
cp -r ../../examples/ecdsa/* tmp
cd tmp
${SAW} -j ecdsa.jar ecdsa.saw
${SAW} -j ecdsa.jar ecdsa-crucible.saw
cd ..
rm -r tmp
