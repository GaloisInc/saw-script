#!/usr/bin/env bash
set -xe

source codebuild/bin/s2n_setup_env.sh
export PATH=/saw-bin:$PATH
exec codebuild/bin/s2n_codebuild.sh
