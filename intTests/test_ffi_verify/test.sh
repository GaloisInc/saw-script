set -e

clang -Wall -Werror -g -c -emit-llvm -o test.bc test.c

$SAW test.saw
