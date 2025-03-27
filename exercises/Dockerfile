FROM ubuntu:24.04

RUN echo 'debconf debconf/frontend select Noninteractive' | debconf-set-selections
RUN apt-get update && apt-get install -y clang-12 make

RUN find /usr/bin/ -name "*-12" -exec basename {} \; | sed "s/\-12//" | xargs -I{} ln -s /usr/bin/'{}'-12 /usr/bin/'{}'

COPY . /workdir

ENTRYPOINT [ "/workdir/ci-entrypoint.sh" ]
CMD [ "/bin/bash" ]
