#!/bin/bash
set -e

while getopts "cr" opt; do
    case $opt in
        c)
            # Remove './tmp', including all previous releases, before staging.
            clean="true"
            ;;
        r)
            release="true"
            ;;
        \?)
            echo "Invalid option: -$OPTARG" >&2
            exit 1
            ;;
    esac
done

DATE=`date +%F`
# Get 'Version' from the .cabal file.
VERSION=`grep Version saw-script.cabal | awk '{print $2}'`

# Warn if 'SYSTEM_DESC' is not defined. The 'SYSTEM_DESC' env var is
# defined as part of the Jenkins node configuration on the Linux
# nodes.
if [ -n "$release" ] ; then
  RELEASE=saw-${VERSION}-${SYSTEM_DESC:-SYSTEM_DESC-IS-NOT-DEFINED}
else
  RELEASE=saw-${VERSION}-${DATE}-${SYSTEM_DESC:-SYSTEM_DESC-IS-NOT-DEFINED}
fi
TARGET=tmp/release/$RELEASE

if [ -n "$clean" ]; then
    rm -rf ./tmp/release
fi
mkdir -p ${TARGET}/bin
mkdir -p ${TARGET}/doc
mkdir -p ${TARGET}/examples
mkdir -p ${TARGET}/include
mkdir -p ${TARGET}/lib

echo Staging ...

BIN=`pwd`/bin

if [ "${OS}" != "Windows_NT" ]; then
  strip "$BIN"/*
fi

cp LICENSE                                    ${TARGET}/LICENSE
cp README.md                                  ${TARGET}/README.md
cp "$BIN"/cryptol                             ${TARGET}/bin
cp "$BIN"/saw                                 ${TARGET}/bin
cp doc/extcore.md                             ${TARGET}/doc
cp doc/tutorial/sawScriptTutorial.pdf         ${TARGET}/doc/tutorial.pdf
cp doc/manual/manual.pdf                      ${TARGET}/doc/manual.pdf
cp -r doc/tutorial/code                       ${TARGET}/doc
cp intTests/jars/galois.jar                   ${TARGET}/lib
cp -r deps/cryptol/lib/*                      ${TARGET}/lib
cp -r examples/*                              ${TARGET}/examples

cd tmp/release
if [ "${OS}" == "Windows_NT" ]; then
  rm -f ${RELEASE}.zip
  7za a -tzip ${RELEASE}.zip -r ${RELEASE}
  echo
  echo "Release package is `pwd`/${RELEASE}.zip"
else
  rm -f ${RELEASE}.tar.gz
  tar cvfz ${RELEASE}.tar.gz ${RELEASE}
  echo
  echo "Release package is `pwd`/${RELEASE}.tar.gz"
fi
