#!/bin/sh
SAW=${SAW:-saw}
set -e

CACHE="test.cache"
rm -rf "$CACHE"
SAW_SOLVER_CACHE_PATH="$CACHE" $SAW test.saw

rm -rf "$CACHE"
SAW_SOLVER_CACHE_PATH="$CACHE" $SAW session1.saw
SAW_SOLVER_CACHE_PATH="$CACHE" $SAW session2.saw
rm -rf "$CACHE"
