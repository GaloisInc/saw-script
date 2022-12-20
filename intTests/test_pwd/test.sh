#!/usr/bin/env bash

set -e

HERE=`pwd`
RES=`echo ':pwd' | $SAW --interactive --no-color`
[[ "$RES" =~ .*"$HERE".* ]]