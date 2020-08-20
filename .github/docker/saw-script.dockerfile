FROM ubuntu:xenial

# This docker image creates an environment in which
# - `cabal build all` succeeds correctly
# - The s2n proofs can be run without issue

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

RUN curl -sSLo ghcup 'https://downloads.haskell.org/~ghcup/0.1.10/x86_64-linux-ghcup-0.1.10' && \
    chmod +x ghcup && \
    mv ghcup /usr/local/bin/ghcup

RUN ghcup install ghc 8.6.5 && ghcup install cabal && ghcup set ghc 8.6.5
ENV PATH=/root/.ghcup/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin
WORKDIR /saw-script
