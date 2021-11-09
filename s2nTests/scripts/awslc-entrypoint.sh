#!/usr/bin/env bash
set -xe

cd /saw-script/aws-lc-verification/SAW
./scripts/install.sh
cp /saw-bin/saw bin/saw
cp /saw-bin/abc bin/abc

export PATH=/saw-script/aws-lc-verification/SAW/bin:$PATH
export CRYPTOLPATH=/saw-script/aws-lc-verification/cryptol-specs

./scripts/entrypoint_check.sh

