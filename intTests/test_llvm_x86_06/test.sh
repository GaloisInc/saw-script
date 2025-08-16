#!/bin/sh
set -e

#yasm -felf64 discoverytest.S
#ld discoverytest.o -o discoverytest
clang -c -emit-llvm test.c
$SAW test.saw
