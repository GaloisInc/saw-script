FROM ubuntu:xenial

RUN apt-get update -y -q && \
    apt-get install -y software-properties-common && \
    add-apt-repository -y ppa:sri-csl/formal-methods && \
    apt-get update -q -y && \
    apt install -y \
    clang-3.9 \
    curl \
    gcc \
    git \
    llvm-3.9 \
    make \
    openjdk-8-jdk \
    sudo \
    unzip \
    wget \
    yasm \
    yices2 \
    zlib1g \
    zlib1g-dev \
    && \
    wget -t 3 https://github.com/Z3Prover/z3/releases/download/z3-4.8.7/z3-4.8.7-x64-ubuntu-16.04.zip && \
    unzip z3-4.8.7-x64-ubuntu-16.04.zip && \
    cp z3-4.8.7-x64-ubuntu-16.04/bin/z3 /usr/local/bin/z3 && \
    rm -rf z3* && \
    rm -rf /var/lib/apt/lists/*

WORKDIR /saw-script
RUN mkdir -p /saw-script && \
    git clone https://github.com/GaloisInc/s2n.git && \
    mkdir -p s2n/test-deps/saw/bin && \
    cd s2n && \
    git checkout cd7282102bf5e65cc8b324c4127c7943c71c8513

ARG ARG_TEST
ARG ARG_LIBCRYPTO
ENV TESTS=$ARG_TEST
ENV S2N_LIBCRYPTO=$ARG_LIBCRYPTO

WORKDIR /saw-script/s2n
RUN echo 'JOBS=1' >> codebuild/bin/jobs.sh
RUN SAW=true SAW_INSTALL_DIR=tmp-saw codebuild/bin/s2n_install_test_dependencies.sh

COPY scripts/s2n-entrypoint.sh /entrypoint.sh
ENTRYPOINT [ "/entrypoint.sh" ]
CMD [ "/bin/bash" ]