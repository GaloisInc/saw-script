FROM ubuntu:xenial

# This docker container creates an environment in which
# - The s2n proofs can be run without issue
# It assumes the existance of /saw-script/bin/{saw,jss}
# populated from a successful cabal build by running
# (in the host environment or the saw-script.dockerfile)
#    cp $(cabal exec which saw) $PWD/bin
#    cp $(cabal exec which jss) $PWD/bin
# and then mounting that directory into this container
# docker run --rm -it -v $PWD:/saw-script <name of this image>

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

ENV TESTS=sawHMAC
WORKDIR /saw-script/s2n
RUN SAW=true SAW_INSTALL_DIR=tmp-saw codebuild/bin/s2n_install_test_dependencies.sh

COPY .github/docker/s2n-entrypoint.sh /entrypoint.sh
ENTRYPOINT [ "/entrypoint.sh" ]
CMD [ "/bin/bash" ]
