set -e

#yasm -felf64 addvar.S
#ld addvar.o -o addvar
clang -c -emit-llvm test.c
$SAW test.saw
