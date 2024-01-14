#!/bin/sh
set -e

clang -c -emit-llvm -g -frecord-command-line test.c
# clang -c -target x86_64 test.c
# ld.lld -o test test.o
clang -o test test.c
$SAW test.saw

