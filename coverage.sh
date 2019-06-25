#!/bin/bash

stack build --coverage

(cd intTests && ./runtests.sh)

hpc sum --output=saw.tix --union --exclude=Main `find intTests -name "*.tix"`

stack hpc report --destdir=coverage saw.tix
