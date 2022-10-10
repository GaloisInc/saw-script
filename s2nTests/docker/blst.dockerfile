FROM ubuntu:22.04
RUN echo 'debconf debconf/frontend select Noninteractive' | debconf-set-selections
RUN apt-get update && apt-get install -y wget unzip git cmake clang llvm golang python3-pip libncurses6 quilt
RUN pip3 install wllvm

RUN git clone https://github.com/GaloisInc/blst-verification.git /workdir && \
    cd /workdir && \
    git checkout f7c50e400d18066cc4849513418c3f407ba3c608 && \
    git config --file=.gitmodules submodule.blst.url https://github.com/supranational/blst && \
    git config --file=.gitmodules submodule.blst_patched.url https://github.com/supranational/blst && \
    git config --file=.gitmodules submodule.blst_bulk_addition.url https://github.com/supranational/blst && \
    git config --file=.gitmodules submodule.cryptol-specs.url https://github.com/GaloisInc/cryptol-specs && \
    git submodule sync && \
    git submodule update --init

WORKDIR /workdir

COPY scripts/blst-entrypoint.sh /entrypoint.sh
ENTRYPOINT [ "/entrypoint.sh" ]
CMD [ "/bin/bash" ]
