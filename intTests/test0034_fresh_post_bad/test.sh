#!/bin/sh
set -e

mkdir -p tmp
cp ../../examples/fresh-post/* tmp
cd tmp
if ! $SAW fresh-post-bad.saw ; then
    exit 0
else
    exit 1
fi
cd ..
rm -r tmp
