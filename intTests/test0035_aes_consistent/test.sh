#!/bin/sh
set -e

mkdir -p tmp
cp ../../examples/aes/* tmp
cd tmp
$SAW aes.saw
cd ..
rm -r tmp
