set -e

#yasm -felf64 increment.S
#ld increment.o -o increment
clang -c -emit-llvm test.c
$SAW test.saw
