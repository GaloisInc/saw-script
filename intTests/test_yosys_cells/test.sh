#!/usr/bin/env bash
SAW=${SAW:-saw}
set -e
for f in test.*.saw; do ${SAW} $f; done
