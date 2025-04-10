FROM ubuntu:24.04

RUN echo 'debconf debconf/frontend select Noninteractive' | debconf-set-selections
RUN apt-get update && apt-get install -y clang-14 make

# symlink clang -> clang-14 for all the clang bins
RUN (cd /usr/bin && ls *-14 | sed 's/-14$//' | awk '{ printf "ln -s %s-14 %s\n", $1, $1 }' | sh)

COPY . /workdir

ENTRYPOINT [ "/workdir/ci-entrypoint.sh" ]
CMD [ "/bin/bash" ]
