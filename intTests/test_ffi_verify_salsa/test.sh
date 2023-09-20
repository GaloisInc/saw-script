set -e

clang -Wall -Werror -g -c -emit-llvm -o salsa.bc salsa.c

CRYPTOLPATH=../../deps/cryptol-specs $SAW salsa.saw
