#!/bin/sh

if ! $SAW unsound_alloc.saw ; then
    exit 0
else
    exit 1
fi
