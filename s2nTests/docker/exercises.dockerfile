FROM ubuntu:22.04

RUN echo 'debconf debconf/frontend select Noninteractive' | debconf-set-selections
RUN apt-get update && apt-get install -y unzip wget

COPY exercises /workdir

ENTRYPOINT [ "/workdir/ci-entrypoint.sh" ]
CMD [ "/bin/bash" ]
