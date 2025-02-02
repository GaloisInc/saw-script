#!/bin/bash

# Add sphinx-build targets to this pattern as appropriate.
SUPPORTED_DOCS="html|latexpdf"

# Commands that do other work / exit before attempting doc generation.
AUX_COMMANDS="clean"

COMMANDS="${SUPPORTED_DOCS}|${AUX_COMMANDS}"
if [[ "${#}" -ne 1 ]] || [[ ! "${1}" =~ ^(${COMMANDS})$ ]]; then
    echo "Usage: ${0} <${COMMANDS}>"
    exit 1
fi

# N.b. Other ${AUX_COMMANDS} should be handled similarly.
if [[ "${1}" == "clean" ]]; then
    echo "Removing '_build'..."
    rm -rf _build
    echo "Removing packaged code examples ('**/code.tar.gz')..."
    rm -rf **/code.tar.gz
    exit
fi

# Begin document generation
DOC_TYPE="${1}"

bash setup_env.sh
. .venv/bin/activate

# For any directories named 'code', create a corresponding code.tar.gz.
# This can be used to provide a download for the entire directory, which is
# useful for tutorials in particular.
for i in **/code; do
    if ! [ -d "${i}" ];
    then
        continue
    fi

    if ! [ -e "${i}/../code.tar.gz" ];
    then
        echo "Packaging probable code example (${i})..."
        tar -czvf "${i}/../code.tar.gz" -C "${i}" .
    fi
done

echo "Generating ${DOC_TYPE}..."
make "${DOC_TYPE}"

shopt -s extglob
if [[ "${DOC_TYPE}" == "latexpdf" ]]; then
    echo "Copying PDFs to doc/pdfs..."
    mkdir -p pdfs
    cp -f _build/latex/!(galois).pdf pdfs
fi
shopt -u extglob
