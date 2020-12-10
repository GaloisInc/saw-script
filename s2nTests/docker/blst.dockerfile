FROM ubuntu:20.04
RUN echo 'debconf debconf/frontend select Noninteractive' | debconf-set-selections
RUN apt-get update
RUN apt-get install -y wget unzip git cmake clang llvm golang python3-pip libncurses5 quilt
RUN pip3 install wllvm

WORKDIR /saw-script
RUN mkdir -p /saw-script && \
    git clone https://github.com/GaloisInc/blst-verification.git && \
    cd blst-verification && \
    git checkout cb8a2c3c57902a957d4a7ac7872fc78e51118262 && \
    git config --file=.gitmodules submodule.blst.url https://github.com/supranational/blst && \
    git submodule sync && \
    git submodule update --init

COPY scripts/blst-entrypoint.sh /entrypoint.sh
ENTRYPOINT [ "/entrypoint.sh" ]
CMD [ "/bin/bash" ]