FROM haskell:8.8.4 AS build
USER root
RUN apt-get update && apt-get install -y wget libncurses-dev libreadline-dev unzip
RUN useradd -m saw
COPY --chown=saw:saw . /home/saw
USER saw
WORKDIR /home/saw
ENV LANG=C.UTF-8 \
    LC_ALL=C.UTF-8
COPY cabal.GHC-8.8.4.config cabal.project.freeze
RUN cabal v2-update && cabal v2-build -j exe:saw-remote-api
RUN mkdir -p /home/saw/rootfs/usr/local/bin
RUN cp $(cabal v2-exec which saw-remote-api) /home/saw/rootfs/usr/local/bin/saw-remote-api
WORKDIR /home/saw//rootfs/usr/local/bin
RUN curl -o solvers.zip -sL "https://github.com/GaloisInc/what4-solvers/releases/download/snapshot-20210917/ubuntu-18.04-bin.zip"
RUN unzip solvers.zip && rm solvers.zip && chmod +x *
USER root
RUN chown -R root:root /home/saw/rootfs

FROM debian:buster-slim
RUN apt-get update \
    && apt-get install -y libgmp10 libgomp1 libffi6 wget libncurses5 unzip openjdk-11-jdk-headless
COPY --from=build /home/saw/rootfs /
RUN useradd -m saw && chown -R saw:saw /home/saw
USER saw
ENV LANG=C.UTF-8 \
    LC_ALL=C.UTF-8
ENTRYPOINT ["/usr/local/bin/saw-remote-api"]
WORKDIR /home/saw
CMD ["http", "--host", "0.0.0.0", "--port", "8080", "/"]
EXPOSE 8080
