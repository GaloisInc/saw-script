#!/bin/sh

set -e

# We want to ensure there isn't a memory store failure and this is caught during type checking of Setup Value
if $SAW bound.saw | grep -q "Memory store failed"; then
    exit 1
else
    exit 0
fi
