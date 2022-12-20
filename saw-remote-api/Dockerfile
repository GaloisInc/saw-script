FROM ubuntu:22.04 AS build
USER root
RUN apt-get update && \
    apt-get install -y \
      # ghcup requirements
      build-essential curl libffi-dev libffi8 libgmp-dev libgmp10 libncurses-dev libncurses6 libtinfo6 \
      # SAW dependencies
      zlib1g-dev \
      # Miscellaneous
      git wget unzip
RUN useradd -m saw
COPY --chown=saw:saw . /home/saw
USER saw
WORKDIR /home/saw
ENV LANG=C.UTF-8 \
    LC_ALL=C.UTF-8
COPY cabal.GHC-8.8.4.config cabal.project.freeze
ENV PATH=/home/saw/ghcup-download/bin:/home/saw/.ghcup/bin:$PATH
RUN mkdir -p /home/saw/ghcup-download/bin && \
    curl -L https://downloads.haskell.org/~ghcup/0.1.17.7/x86_64-linux-ghcup-0.1.17.7 -o /home/saw/ghcup-download/bin/ghcup && \
    chmod +x /home/saw/ghcup-download/bin/ghcup
RUN mkdir -p /home/saw/.ghcup && \
    ghcup --version && \
    ghcup install cabal 3.6.2.0 && \
    ghcup install ghc 8.8.4 && \
    ghcup set ghc 8.8.4
RUN cabal v2-update && cabal v2-build -j exe:saw-remote-api
RUN mkdir -p /home/saw/rootfs/usr/local/bin
RUN cp $(cabal v2-exec which saw-remote-api) /home/saw/rootfs/usr/local/bin/saw-remote-api
WORKDIR /home/saw//rootfs/usr/local/bin
RUN curl -o solvers.zip -sL "https://github.com/GaloisInc/what4-solvers/releases/download/snapshot-20221212/ubuntu-22.04-bin.zip"
RUN unzip solvers.zip && rm solvers.zip && chmod +x *
USER root
RUN chown -R root:root /home/saw/rootfs

FROM ubuntu:22.04
RUN apt-get update && \
    apt-get install -y libgmp10 libgomp1 libffi8 wget libncurses6 unzip libreadline-dev openjdk-11-jdk-headless
COPY --from=build /home/saw/rootfs /
RUN useradd -m saw && chown -R saw:saw /home/saw
USER saw
ENV LANG=C.UTF-8 \
    LC_ALL=C.UTF-8
ENTRYPOINT ["/usr/local/bin/saw-remote-api"]
WORKDIR /home/saw
CMD ["http", "--host", "0.0.0.0", "--port", "8080", "/"]
EXPOSE 8080
