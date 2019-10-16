#!/bin/sh
set -e

mkdir -p tmp
cp -r ../../examples tmp

(cd tmp/examples &&
for f in `find fresh-post ghost java llvm multi-override partial-spec salsa20 -name "*.saw"` ; do
    (cd `dirname $f` && $SAW `basename $f`)
done)

(cd ../../examples &&
for f in `find aes salsa20 -name "*.saw"` ; do
    (cd `dirname $f` && $SAW `basename $f`)
done)

rm -r tmp
