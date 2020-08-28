FROM ubuntu:18.04

RUN apt-get update -y -q && \
    apt-get install -y software-properties-common && \
    apt-get update -q -y && \
    apt install -y \
    clang-3.9 \
    curl \
    gcc \
    git \
    llvm-3.9 \
    make \
    sudo \
    && \
    rm -rf /var/lib/apt/lists/*

WORKDIR /saw-script
RUN mkdir -p /saw-script && \
    git clone https://github.com/GaloisInc/s2n.git && \
    mkdir -p s2n/test-deps/saw/bin && \
    cd s2n && \
    git checkout 90b8913a01c6421444d19aaab798d413872cf6f0

COPY scripts/s2n-entrypoint.sh /entrypoint.sh
ENTRYPOINT [ "/entrypoint.sh" ]
CMD [ "/bin/bash" ]