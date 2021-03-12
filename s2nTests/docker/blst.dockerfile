FROM ubuntu:20.04
RUN echo 'debconf debconf/frontend select Noninteractive' | debconf-set-selections
RUN apt-get update && apt-get install -y wget unzip git cmake clang llvm golang python3-pip libncurses5 quilt
RUN pip3 install wllvm

RUN git clone https://github.com/GaloisInc/blst-verification.git /workdir && \
    cd /workdir && \
    git checkout 05d29b0e9d826053185e5bdba287045aab0b4669 && \
    git config --file=.gitmodules submodule.blst.url https://github.com/supranational/blst && \
    git submodule sync && \
    git submodule update --init

WORKDIR /workdir

COPY scripts/blst-entrypoint.sh /entrypoint.sh
ENTRYPOINT [ "/entrypoint.sh" ]
CMD [ "/bin/bash" ]