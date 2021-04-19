#!/bin/sh
set -e

# yasm -felf64 test.S
# ld test.o -o test
clang -c -emit-llvm test.c
$SAW test.saw
