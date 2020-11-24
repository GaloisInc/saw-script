FROM ubuntu:20.04

ARG heapster_commit=ca697c01ae9f3d2fbcae3169318d69f58e83efb2

ENV PATH="/home/heapster/.local/bin:/home/heapster/.cabal/bin:/home/heapster/.ghcup/bin:${PATH}"
ENV OPAMYES="true"

# Dependencies for installing Haskell and Coq, mainly
RUN apt-get update && apt-get install -y \
  curl gcc git m4 make libtinfo5 libgmp-dev locales locales-all opam xz-utils z3 zlib1g-dev 

ENV LC_ALL en_US.UTF-8
ENV LANG en_US.UTF-8
ENV LANGUAGE en_US.UTF-8

# Running GHCUP and Opam don't like to run as root
RUN useradd -ms /bin/bash heapster
USER heapster

# Install Coq and libraries
RUN opam init --disable-sandboxing -a && eval $(opam env) && \
  opam switch create with-coq 4.09.1 && \
  opam pin -y add coq 8.12.1 && eval $(opam env) && \
  opam repo add coq-released https://coq.inria.fr/opam/released && \
  opam update && opam install -y coq-bits

# Install GHCUP, and use that to install GHC and Cabal
RUN mkdir -p ~/.ghcup/bin && \
  curl https://downloads.haskell.org/~ghcup/x86_64-linux-ghcup > /home/heapster/.ghcup/bin/ghcup && \
  chmod +x /home/heapster/.ghcup/bin/ghcup && \
  ghcup install 8.6.5 && ghcup set 8.6.5 && \
  ghcup install-cabal 3.2.0.0 && \
  cabal update

# Build and install SAW
WORKDIR /home/heapster
# Necessary to deal with SSH URLs in some submodules
RUN git config --global url."https://github.com/".insteadOf git@github.com: && \
  git config --global url."https://".insteadOf git://
RUN git clone https://github.com/GaloisInc/saw-script.git && \
  cd saw-script && \
  git checkout ${heapster_commit} && \
  git submodule update --init --recursive && \
  ln -sf cabal.GHC-8.6.5.config cabal.project.freeze && \
  cabal build && \
  mkdir -p /home/heapster/.local/bin && \
  ln -sf `cabal exec which saw` /home/heapster/.local/bin/saw

RUN eval $(opam env) && cd /home/heapster/saw-script/deps/saw-core-coq/coq && make