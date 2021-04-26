#!/bin/sh

if ! $SAW unsound_global.saw ; then
    exit 0
else
    exit 1
fi
