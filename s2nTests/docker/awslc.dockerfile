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

# The commit we check out is now the head of the saw-test-runs branch,
# because we added that commit (and branch) specifically to fix up
# some problems with this test run. Prior to that the commit was the
# head of the sb/functors-ci-pin branch. It is no longer clear at this
# point (January 2025) why that particular branch was chosen (there
# are many) or how it relates to the upstream state of the repository
# (our copy in GaloisInc is a fork repo).
#
# We're using the specific commit hash rather than the branch (even
# though the branch is now specific to what we're doing here) so it
# doesn't silently update on us if/when we start tidying up over
# there.

WORKDIR /saw-script
RUN mkdir -p /saw-script && \
    git clone https://github.com/GaloisInc/aws-lc-verification.git && \
    cd aws-lc-verification && \
    git checkout f2570467f0d8ce21df00b3cf3ccc325656d77b4e && \
    git config --file=.gitmodules submodule.src.url https://github.com/awslabs/aws-lc && \
    git submodule sync && \
    git submodule update --init

COPY scripts/awslc-entrypoint.sh /entrypoint.sh
ENTRYPOINT [ "/entrypoint.sh" ]
CMD [ "/bin/bash" ]
