#!/usr/bin/env bash
# Postprocess script for test_offline_coq. Outputs the SAW execution output
# followed by the generated Coq files.

cat
for file in test_offline_coq*_prove*.v; do
    if [ -f "$file" ]; then
        echo "=== $file ==="
        cat "$file"
        echo
    fi
done
