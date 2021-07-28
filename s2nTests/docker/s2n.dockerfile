# Note: this Dockerfile will be used to run the saw binary built by
# the CI process, which means that the loadable libraries should be
# the same between the two systems.  This stipulates that the "FROM"
# instance specified here should match the OS image used to perform
# the build stage (whether that's a Github runner or a self-hosted
# runner).
#
# A common symptom of these not matching is that the bin/saw image
# cannot be run because libtinfoX.so is not found.

FROM ubuntu:20.04

RUN apt-get update -y -q && \
    apt-get install -y software-properties-common && \
    apt-get update -q -y && \
    apt install -y \
    clang-5 \
    curl \
    gcc \
    git \
    llvm-5 \
    make \
    sudo \
    && \
    rm -rf /var/lib/apt/lists/*

WORKDIR /saw-script
RUN mkdir -p /saw-script && \
    git clone https://github.com/GaloisInc/s2n.git && \
    mkdir -p s2n/test-deps/saw/bin && \
    cd s2n && \
    git checkout 6586f1ad3b35efcd2287ab98a4be124449dcb780



COPY scripts/s2n-entrypoint.sh /entrypoint.sh
ENTRYPOINT [ "/entrypoint.sh" ]
CMD [ "/bin/bash" ]