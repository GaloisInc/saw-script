# Note: before running "docker build", you should do "./build.sh
# gitrev" so that the current git commit information propagates
# into the container.

# Note that we intentionally do not use ubuntu:24.04 or later pending a
# resolution to https://github.com/coder/coder/issues/17316.
FROM ubuntu:22.04 AS build
USER root
RUN apt-get update && \
    apt-get install -y \
      # ghcup requirements
      build-essential curl libffi-dev libffi8 libgmp-dev libgmp10 libncurses-dev libncurses6 libtinfo6 \
      # Although ghcup's version of GHC shouldn't require libnuma, the aarch64 \
      # version does impose this requirement for unknown reasons. \
      # (See https://gitlab.haskell.org/ghc/ghc/-/issues/20876#note_399802) \
      libnuma1 \
      # SAW dependencies
      pkg-config zlib1g-dev \
      # Miscellaneous
      git wget unzip
RUN useradd -m saw
COPY --chown=saw:saw . /home/saw
USER saw
WORKDIR /home/saw
ENV LANG=C.UTF-8 \
    LC_ALL=C.UTF-8
COPY cabal.GHC-9.6.7.config cabal.project.freeze
ENV PATH=/home/saw/ghcup-download/bin:/home/saw/.ghcup/bin:$PATH
ARG TARGETPLATFORM
RUN case ${TARGETPLATFORM} in \
      "linux/amd64") \
        GHCUP_ARCH=x86_64 ;; \
      "linux/arm64" | "linux/arm64/v8") \
        GHCUP_ARCH=aarch64 ;; \
      *) \
        printf "Unsupported architecture: %s\n" "${TARGETPLATFORM}" >&2 \
        exit 1 ;; \
    esac && \
    mkdir -p /home/saw/ghcup-download/bin && \
    curl -L https://downloads.haskell.org/~ghcup/0.1.50.2/${GHCUP_ARCH}-linux-ghcup-0.1.50.2 -o /home/saw/ghcup-download/bin/ghcup && \
    chmod +x /home/saw/ghcup-download/bin/ghcup
RUN mkdir -p /home/saw/.ghcup && \
    ghcup --version && \
    ghcup install cabal 3.10.3.0 && \
    ghcup install ghc 9.6.7 && \
    ghcup set ghc 9.6.7

# Make sure GitRev.hs exists in case it wasn't created outside the
# container and copied in. Since we don't have .git in here, this will
# not overwrite an existing GitRev.hs, but it will create a blank one
# if it's missing entirely. That in turn will avoid an unnecessary
# build failure.
RUN ./build.sh gitrev

RUN cabal v2-update && cabal v2-build -j exe:saw-remote-api
RUN mkdir -p /home/saw/rootfs/usr/local/bin
RUN cp $(cabal -v0 list-bin exe:saw-remote-api) /home/saw/rootfs/usr/local/bin/saw-remote-api
WORKDIR /home/saw//rootfs/usr/local/bin
# The URL here is based on the same logic used to specify BUILD_TARGET_OS and
# BUILD_TARGET_ARCH in `.github/workflow/ci.yml`, but specialized to Ubuntu.
# If updating the snapshot version, update ci.yml and saw/Dockerfile too.
RUN case ${TARGETPLATFORM} in \
      "linux/amd64") \
        WHAT4_SOLVERS_ARCH=X64 ;; \
      "linux/arm64" | "linux/arm64/v8") \
        WHAT4_SOLVERS_ARCH=ARM64 ;; \
      *) \
        printf "Unsupported architecture: %s\n" "${TARGETPLATFORM}" >&2 \
        exit 1 ;; \
    esac && \
    curl -o solvers.zip -sL "https://github.com/GaloisInc/what4-solvers/releases/download/snapshot-20251112/ubuntu-22.04-${WHAT4_SOLVERS_ARCH}-bin.zip"
RUN unzip solvers.zip && rm solvers.zip && chmod +x *
USER root
RUN chown -R root:root /home/saw/rootfs

FROM ubuntu:22.04
RUN apt-get update && \
    apt-get install -y libgmp10 libgomp1 libffi8 wget libncurses6 unzip libreadline-dev openjdk-11-jdk-headless zlib1g
COPY --from=build /home/saw/rootfs /
RUN useradd -m saw && chown -R saw:saw /home/saw
USER saw
ENV LANG=C.UTF-8 \
    LC_ALL=C.UTF-8
ENTRYPOINT ["/usr/local/bin/saw-remote-api"]
WORKDIR /home/saw
CMD ["http", "--host", "0.0.0.0", "--port", "8080", "/"]
EXPOSE 8080
