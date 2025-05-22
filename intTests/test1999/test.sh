#!/bin/sh

failures=0

for script in *.saw; do
  echo "Running $script"
  $SAW "$script" || { echo "FAILED: $script"; failures=1; true; }
done

exit $failures
