FROM ubuntu:20.04
RUN echo 'debconf debconf/frontend select Noninteractive' | debconf-set-selections
RUN apt-get update
RUN apt-get install -y wget unzip git cmake clang llvm golang python3-pip libncurses5 quilt
RUN pip3 install wllvm

WORKDIR /saw-script
RUN mkdir -p /saw-script && \
    git clone https://github.com/GaloisInc/aws-lc-verification.git && \
    cd aws-lc-verification && \
    git checkout 2a5598300748cbc6b5aac9ba2b44bd2982324763 && \
    git config --file=.gitmodules submodule.src.url https://github.com/awslabs/aws-lc && \
    git submodule sync && \
    git submodule update --init

COPY scripts/awslc-entrypoint.sh /entrypoint.sh
ENTRYPOINT [ "/entrypoint.sh" ]
CMD [ "/bin/bash" ]