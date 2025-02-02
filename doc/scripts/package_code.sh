#!/bin/sh

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
