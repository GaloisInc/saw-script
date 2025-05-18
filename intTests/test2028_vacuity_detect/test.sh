#!/bin/bash

n=$( "$SAW" --detect-vacuity test.saw 2>&1 | tee /dev/stderr | grep -c "Contradiction detected" )

if [ "$n" -eq 3 ]; then
  echo "Found 3 expected contradictions"
  exit 0
else
  echo "Expected 3 contradictions, found $n"
  exit 1
fi
