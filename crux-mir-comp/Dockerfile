# Note: before running "docker build", you should do "./build.sh
# gitrev" so that the current git commit information propagates
# into the container.

ARG RUST_TOOLCHAIN="nightly-2025-02-16"

# Note that we intentionally do not use ubuntu:24.04 or later pending a
# resolution to https://github.com/coder/coder/issues/17316.
FROM ubuntu:22.04 AS build
ARG RUST_TOOLCHAIN

USER root
RUN apt-get update && \
    apt-get install -y \
      # ghcup requirements
      build-essential curl libffi-dev libffi8 libgmp-dev libgmp10 libncurses-dev libncurses6 libtinfo6 \
      # Although ghcup's version of GHC shouldn't require libnuma, the aarch64 \
      # version does impose this requirement for unknown reasons. \
      # (See https://gitlab.haskell.org/ghc/ghc/-/issues/20876#note_399802) \
      libnuma1 \
      # crux-mir-comp dependencies \
      pkg-config zlib1g-dev \
      # Miscellaneous
      git unzip wget
RUN useradd -m crux-mir-comp
COPY --chown=crux-mir-comp:crux-mir-comp . /home/crux-mir-comp
USER crux-mir-comp
WORKDIR /home/crux-mir-comp
ENV LANG=C.UTF-8 \
    LC_ALL=C.UTF-8
COPY cabal.GHC-9.4.8.config cabal.project.freeze
ENV PATH=/home/crux-mir-comp/rootfs/usr/local/bin:/home/crux-mir-comp/.cargo/bin:/home/crux-mir-comp/.local/bin:/home/crux-mir-comp/ghcup-download/bin:/home/crux-mir-comp/.ghcup/bin:$PATH

WORKDIR /home/crux-mir-comp/deps/mir-json
RUN curl https://sh.rustup.rs -sSf | bash -s -- -y --profile minimal --default-toolchain ${RUST_TOOLCHAIN}
RUN rustup component add --toolchain ${RUST_TOOLCHAIN} rustc-dev rust-src
RUN cargo install --locked && \
    mir-json-translate-libs
# Define `CRUX_RUST_LIBRARY_PATH` this for the benefit of
# `cabal v2-test crux-mir-comp` below.
ENV CRUX_RUST_LIBRARY_PATH=/home/crux-mir-comp/deps/mir-json/rlibs

RUN mkdir -p /home/crux-mir-comp/rootfs/usr/local/bin
WORKDIR /home/crux-mir-comp/rootfs/usr/local/bin
# The URL here is based on the same logic used to specify BUILD_TARGET_OS and
# BUILD_TARGET_ARCH in `.github/workflow/ci.yml`, but specialized to Ubuntu.
# If updating the snapshot version, update ci.yml and crux-mir-comp/Dockerfile too.
ARG TARGETPLATFORM
RUN case ${TARGETPLATFORM} in \
      "linux/amd64") \
        WHAT4_SOLVERS_ARCH=X64 ;; \
      "linux/arm64" | "linux/arm64/v8") \
        WHAT4_SOLVERS_ARCH=ARM64 ;; \
      *) \
        printf "Unsupported architecture: %s\n" "${TARGETPLATFORM}" >&2 \
        exit 1 ;; \
    esac && \
    curl -o solvers.zip -sL "https://github.com/GaloisInc/what4-solvers/releases/download/snapshot-20250606/ubuntu-22.04-${WHAT4_SOLVERS_ARCH}-bin.zip"
RUN unzip solvers.zip && rm solvers.zip && chmod +x *

WORKDIR /home/crux-mir-comp
RUN case ${TARGETPLATFORM} in \
      "linux/amd64") \
        GHCUP_ARCH=x86_64 ;; \
      "linux/arm64" | "linux/arm64/v8") \
        GHCUP_ARCH=aarch64 ;; \
      *) \
        printf "Unsupported architecture: %s\n" "${TARGETPLATFORM}" >&2 \
        exit 1 ;; \
    esac && \
    mkdir -p /home/crux-mir-comp/ghcup-download/bin && \
    curl -L https://downloads.haskell.org/~ghcup/0.1.19.5/${GHCUP_ARCH}-linux-ghcup-0.1.19.5 -o /home/crux-mir-comp/ghcup-download/bin/ghcup && \
    chmod +x /home/crux-mir-comp/ghcup-download/bin/ghcup
RUN mkdir -p /home/crux-mir-comp/.ghcup && \
    ghcup --version && \
    ghcup install cabal 3.10.3.0 && \
    ghcup install ghc 9.4.8 && \
    ghcup set ghc 9.4.8

# Make sure GitRev.hs exists in case it wasn't created outside the
# container and copied in. Since we don't have .git in here, this will
# not overwrite an existing GitRev.hs, but it will create a blank one
# if it's missing entirely. That in turn will avoid an unnecessary
# build failure.
RUN ./build.sh gitrev

RUN cabal update && \
    cabal build -j exe:crux-mir-comp && \
    cabal test crux-mir-comp
RUN cp $(cabal -v0 list-bin exe:crux-mir-comp) /home/crux-mir-comp/rootfs/usr/local/bin/crux-mir-comp
USER root
RUN chown -R root:root /home/crux-mir-comp/rootfs

FROM ubuntu:22.04
RUN apt-get update && \
    apt-get install -y \
      libgmp10 libgomp1 libffi8 wget libncurses6 libreadline-dev unzip zlib1g libcurl4 \
      # A C toolchain (needed to build crates that require a C compiler)
      clang

COPY --from=build /home/crux-mir-comp/.cargo/bin /home/crux-mir-comp/.cargo/bin
COPY --from=build /home/crux-mir-comp/.rustup /home/crux-mir-comp/.rustup
COPY --from=build /home/crux-mir-comp/rootfs /
COPY --from=build /home/crux-mir-comp/deps/mir-json/rlibs /crux-mir-comp/rlibs

RUN useradd -m crux-mir-comp && chown -R crux-mir-comp:crux-mir-comp /crux-mir-comp /home/crux-mir-comp
USER crux-mir-comp
WORKDIR /

ENV LANG=C.UTF-8 \
    LC_ALL=C.UTF-8 \
    PATH=/home/crux-mir-comp/.cargo/bin:$PATH \
    CRUX_MIR=/usr/local/bin/crux-mir-comp \
    CRUX_RUST_LIBRARY_PATH=/crux-mir-comp/rlibs

ENTRYPOINT ["/home/crux-mir-comp/.cargo/bin/cargo", "crux-test"]
