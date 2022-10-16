FROM ubuntu:22.04
RUN echo 'debconf debconf/frontend select Noninteractive' | debconf-set-selections
RUN apt-get update && apt-get install -y curl wget unzip git cmake golang python3-pip libncurses6 libncurses5 libtinfo-dev quilt file
RUN pip3 install wllvm
RUN curl -OL https://github.com/llvm/llvm-project/releases/download/llvmorg-10.0.0/clang+llvm-10.0.0-x86_64-linux-gnu-ubuntu-18.04.tar.xz && \
    tar xf clang+llvm-10.0.0-x86_64-linux-gnu-ubuntu-18.04.tar.xz && \
    cp -r clang+llvm-10.0.0-x86_64-linux-gnu-ubuntu-18.04/* /usr

WORKDIR /saw-script
RUN mkdir -p /saw-script && \
    git clone https://github.com/GaloisInc/aws-lc-verification.git && \
    cd aws-lc-verification && \
    git checkout 1dcf4258305ce17592fb5b90a1c7b638e6bdff9e && \
    git config --file=.gitmodules submodule.src.url https://github.com/awslabs/aws-lc && \
    git submodule sync && \
    git submodule update --init

COPY scripts/awslc-entrypoint.sh /entrypoint.sh
ENTRYPOINT [ "/entrypoint.sh" ]
CMD [ "/bin/bash" ]
