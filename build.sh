#!/bin/bash
set -x
set -v
set -e

TESTABLE="abcBridge jvm-verifier parameterized-utils saw-core"

dotests="false"
jobs=""
while getopts "tpfj:" opt; do
    case $opt in
        t)
            dotests="true"
            ;;
        j)
            jobs="-j$OPTARG"
            ;;
        \?)
            echo "Invalid option: -$OPTARG" >&2
            exit 1
            ;;
    esac
done

git submodule init
git submodule update

if [ ! -e stack.yaml -a -z "$STACK_YAML" ] ; then
    set +x
    echo
    echo "ERROR: no stack.yaml file found."
    echo
    echo "Select one of the given stack configuration files using:"
    echo
    echo "    ln -s stack.<ghc version and os>.yaml stack.yaml"
    exit 1
fi

stack setup

LOCALBINPATH=$(stack path --local-bin-path | tr -d '\r\n')
if [ "${OS}" == "Windows_NT" ] ; then
    HERE=$(cygpath -w $(pwd))
    PATH=$PATH:$(cygpath -u -a $LOCALBINPATH)
else
    HERE=$(pwd)
    PATH=$PATH:$LOCALBINPATH
fi

stack="stack $jobs"

${stack} install alex
${stack} install happy
${stack} install c2hs

which alex
which happy
which c2hs

if [ "${dotests}" == "true" ] ; then
  if [ -z ${TEST_TIMEOUT} ]; then
    TEST_TIMEOUT="120s"
  fi

  mkdir -p tmp
  for pkg in ${TESTABLE}; do
    test_arguments="--xml=${HERE}/tmp/${pkg}-test-results.xml --timeout=${TEST_TIMEOUT}"

    if [ ! "${QC_TESTS}" == "" ]; then
        test_arguments="${test_arguments} --quickcheck-tests=${QC_TESTS}"
    fi

    # Stack is returning 1 when a test fails, which kills the whole
    # build. Presumably Cabal returned 0 in this case.
    #
    # If the build part of the test fails, there won't be any XML
    # file, so we'll detect failure in that case when we check for the
    # XML file below.
    (
      set +e
      ${stack} build --test --test-arguments="${test_arguments}" ${pkg}
      exit 0
    )

    if [ -e tmp/${pkg}-test-results.xml ]; then
      xsltproc jenkins-junit-munge.xsl tmp/${pkg}-test-results.xml > tmp/jenkins-${pkg}-test-results.xml
    else
      echo "Missing test results: tmp/${pkg}-test-results.xml"
      exit 1
    fi
  done
else
  ${stack} build
fi

# Link bin directory to a more convenient location
rm -f bin
ln -s `stack path --local-install-root`/bin
set +x +v
echo
echo "COPIED EXECUTABLES TO `pwd`/bin."
