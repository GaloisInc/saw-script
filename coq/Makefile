all: build

Makefile.coq: _CoqProject
	coq_makefile -f $< -o $@

build: Makefile.coq
	make -f Makefile.coq
