FROM ubuntu:22.04

RUN apt-get update -y -q && \
    apt-get install -y software-properties-common && \
    apt-get update -q -y && \
    apt install -y \
    curl \
    gcc \
    g++ \
    git \
    make \
    sudo \
    unzip \
    indent \
    kwstyle \
    libssl-dev \
    tcpdump \
    valgrind \
    lcov \
    m4 \
    nettle-dev \
    nettle-bin \
    pkg-config \
    zlib1g-dev \
    python3-pip \
    tox \
    libncurses5 \
    libtinfo-dev \
    && \
    rm -rf /var/lib/apt/lists/*
RUN curl -OL https://releases.llvm.org/3.9.0/clang+llvm-3.9.0-x86_64-linux-gnu-ubuntu-16.04.tar.xz && \
    tar xf clang+llvm-3.9.0-x86_64-linux-gnu-ubuntu-16.04.tar.xz && \
    cp -r clang+llvm-3.9.0-x86_64-linux-gnu-ubuntu-16.04/* /usr

WORKDIR /saw-script
RUN mkdir -p /saw-script && \
    git clone https://github.com/GaloisInc/s2n.git && \
    mkdir -p s2n/test-deps/saw/bin && \
    cd s2n && \
    git checkout 6586f1ad3b35efcd2287ab98a4be124449dcb780



COPY scripts/s2n-entrypoint.sh /entrypoint.sh
ENTRYPOINT [ "/entrypoint.sh" ]
CMD [ "/bin/bash" ]
