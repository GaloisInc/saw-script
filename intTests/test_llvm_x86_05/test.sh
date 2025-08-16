set -e

#yasm -felf64 returntest.S
#ld returntest.o -o returntest
clang -c -emit-llvm test.c
$SAW test.saw
