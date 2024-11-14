#!/usr/bin/env bash

set -e

HERE=`pwd`
RES=`printf '%s\n%s\n%s\n' ':pwd' 'include "err/err.saw"' ':pwd' | \
    $SAW --interactive --no-color | \
    sed -r '/^\s*$/d' | \
    sort | \
    uniq -d`
[[ "$RES" =~ .*"$HERE"$.* ]]
