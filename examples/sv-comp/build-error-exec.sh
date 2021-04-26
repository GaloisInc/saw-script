#!/bin/sh
bc=$1
base=`basename $1 .bc`
saw ${base}.saw &> ${base}.log
cex=`grep "\"x\"" ${base}.log | cut -d , -f 2 | sed -e "s/)/,/"`
echo "unsigned int uints[] = { $cex };" >> ${base}-cex.c
cat sv-comp-lib.c >> ${base}-cex.c
clang -g -o ${base} ${base}.bc ${base}-cex.c
rm -f ${base}.log ${base}-cex.c
