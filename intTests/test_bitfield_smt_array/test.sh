#!/usr/bin/env bash

set -e

# llvm_points_to_bitfield and enable_smt_array_memory_model currently do not
# mix. See #1540.
! $SAW test.saw
