#!/bin/bash
COMMANDS="wget clang javac saw"
for COMMAND in ${COMMANDS}; do
        type -P ${COMMAND} &>/dev/null && continue || { >&2 echo "${COMMAND} command not found."; exit 1; }
done
if [ -z "$JAVA_HOME" ]; then
    echo "Need to set JAVA_HOME environment variable"
    exit 1
fi
if [ ! -e simon.cry ]; then
  wget -q https://github.com/GaloisInc/cryptol/raw/master/examples/contrib/simon.cry
fi
if [ ! -e speck.cry ]; then
  wget -q https://github.com/GaloisInc/cryptol/raw/master/examples/contrib/speck.cry
fi
rm -f simon-64-128 simon-128-128 speck-64-128 speck-128-128 *.bc *.class
clang -DN=32 -o speck-64-128 speck.c
clang -DSAW=1 -DN=32 -c -emit-llvm -o speck-64-128.bc speck.c
clang -DN=64 -o speck-128-128 speck.c
clang -DSAW=1 -DN=64 -c -emit-llvm -o speck-128-128.bc speck.c
clang -o simon-64-128 simon-64-128.c
clang -c -emit-llvm -o simon-64-128.bc simon-64-128.c
clang -o simon-128-128 simon-128-128.c
clang -c -emit-llvm -o simon-128-128.bc simon-128-128.c
javac -g SimonEngine.java
javac -g SpeckEngine.java
saw simon.saw
saw speck.saw
saw -b $JAVA_HOME/bin speck-java-bug-1.saw
saw -b $JAVA_HOME/bin speck-java-bug-2.saw
