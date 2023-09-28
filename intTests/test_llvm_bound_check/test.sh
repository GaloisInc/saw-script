#!/bin/sh

set -e

# We want to ensure there isn't a memory store failure and this is caught during type checking of Setup Value
if $SAW bound.saw | grep -q "array type index out of bounds"; then
    exit 0
else
    exit 1
fi
