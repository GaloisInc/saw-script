#!/bin/sh
set -e

# yasm -felf64 precondtest.S
# ld precondtest.o -o precondtest
clang -c -emit-llvm test.c
$SAW test.saw
