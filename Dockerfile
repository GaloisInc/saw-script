FROM haskell:8.6 AS build
USER root
# TODO: install Yices, too (and CVC4?, Boolector?)
RUN apt-get update \
    && apt-get install -y wget libncurses-dev unzip \
    && wget https://github.com/Z3Prover/z3/releases/download/z3-4.7.1/z3-4.7.1-x64-debian-8.10.zip \
    && unzip z3*.zip \
    && mv z3-*/bin/z3 /usr/local/bin
RUN useradd -m saw
RUN su -c '/opt/cabal/bin/cabal v2-update' saw
ADD saw-script.tar.gz /home/saw
RUN chown -R saw:saw /home/saw/saw-script
USER saw
WORKDIR /home/saw/saw-script
RUN cp cabal.project.GHC-8.6.freeze cabal.project.freeze
RUN cabal v2-build
WORKDIR /home/saw
RUN mkdir -p rootfs/usr/local/bin \
    && cp /usr/local/bin/z3 rootfs/usr/local/bin/z3 \
    && cp saw-script/dist-newstyle/build/*-linux/ghc-*/saw-script-*/build/saw/saw rootfs/usr/local/bin/saw
USER root
RUN chown -R root:root /home/saw/rootfs

FROM debian:stretch-slim
RUN apt-get update \
    && apt-get install -y libgmp10 libgomp1 libffi6 wget libncurses5 unzip
COPY --from=build /home/saw/rootfs /
RUN useradd -m saw && chown -R saw:saw /home/saw
USER saw
ENTRYPOINT ["/usr/local/bin/saw"]
