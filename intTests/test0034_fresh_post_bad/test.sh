#!/bin/sh
set -e

mkdir -p tmp
cp ../../examples/fresh-post/* tmp
cd tmp
$SAW fresh-post-bad.saw
cd ..
rm -r tmp
