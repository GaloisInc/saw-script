#!/bin/sh
set -e
export CRYPTOLPATH="../../deps/cryptol-specs"
(cd ../../examples &&
for f in `find aes fresh-post ghost java llvm multi-override partial-spec -name "*.saw"` ; do
    (cd `dirname $f` && $SAW `basename $f`)
done)

(cd ../../examples/salsa20 && $SAW salsa.saw)
