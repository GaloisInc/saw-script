#!/bin/sh
timeout -k 5s 10s $SAW test.saw
if [ $? -eq 124 ]; then
  echo "Timed out"
  exit 1
fi