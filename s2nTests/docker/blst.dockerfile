FROM ubuntu:24.04
RUN echo 'debconf debconf/frontend select Noninteractive' | debconf-set-selections
RUN apt-get update && apt-get install -y curl wget unzip git cmake golang python3-pip libncurses6 libtinfo-dev quilt file clang-14
# FUTURE: Apparently you're now supposed to install a venv and not try
# to use pip to install system-wide packages. --break-system-packages
# is probably ok as a workaround here but it wouldn't surprise me if
# it disappeared after a while.
RUN pip3 install --break-system-packages wllvm

# This doesn't run any more on ubuntu 24.04 (it's linked to ncurses 5)
# so we're going to install clang-14 (the oldest in said ubuntu) instead
# and hope it works.
#
#RUN curl -OL https://github.com/llvm/llvm-project/releases/download/llvmorg-10.0.0/clang+llvm-10.0.0-x86_64-linux-gnu-ubuntu-18.04.tar.xz && \
#    tar xf clang+llvm-10.0.0-x86_64-linux-gnu-ubuntu-18.04.tar.xz && \
#    cp -r clang+llvm-10.0.0-x86_64-linux-gnu-ubuntu-18.04/* /usr

# symlink clang -> clang-14 for all the clang bins
RUN (cd /usr/bin && ls *-14 | sed 's/-14$//' | awk '{ printf "ln -s %s-14 %s\n", $1, $1 }' | sh)

# The commit we check out is the head of the main branch.
#
# We're using the specific commit hash (rather than checking out main)
# so it doesn't update under us unexpectedly.

RUN git clone https://github.com/GaloisInc/blst-verification.git /workdir && \
    cd /workdir && \
    git checkout 977dfeb420ca578fad644d2725f56f711999665b && \
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
