#!/usr/bin/env bash
# Postprocess script for test_offline_rocq. Outputs the SAW execution output
# followed by the generated Rocq files.

cat
for file in test_offline_rocq*_prove*.v; do
    if [ -f "$file" ]; then
        echo "=== $file ==="
        cat "$file"
        echo
    fi
done
