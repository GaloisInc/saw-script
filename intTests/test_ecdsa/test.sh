#!/bin/sh
set -e

JDK=`(java -verbose 2>&1) | grep Opened | head -1 | cut -d ' ' -f 2 | cut -d ']' -f 1`
mkdir -p tmp
cp -r ../../examples/ecdsa/* tmp
cd tmp
${SAW} -j ${JDK} -j ecdsa.jar ecdsa.saw
cd ..
rm -r tmp
