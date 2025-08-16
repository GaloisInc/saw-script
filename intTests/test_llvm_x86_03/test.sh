set -e

#yasm -felf64 foo.S
#ld foo.o -o foo
clang -c -emit-llvm bar.c
$SAW test.saw
