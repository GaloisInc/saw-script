#!/bin/sh
set -e

cp ../../examples/aes/aes.saw .
$SAW aes.saw
rm -f aes.saw
