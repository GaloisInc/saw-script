#!/bin/bash

saw_files=("test_mir.saw" "test_llvm.saw" "test_jvm.saw")
total=0

for f in "${saw_files[@]}"; do
  out=$( $SAW "$f" 2>&1 | tee /dev/stderr )
  count=$( echo "$out" | grep -c "Expected type Bit, got" )
  total=$((total + count))
done

if [ "$total" -eq 3 ]; then
  echo "Found 3 expected type errors"
  exit 0
else
  echo "Expected 3 type errors, found $total"
  exit 1
fi

