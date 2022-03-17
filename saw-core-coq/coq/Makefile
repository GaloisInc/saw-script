all: Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f $< -o $@

include Makefile.coq

# If running in CI, always set $SAW=`which saw`. Otherwise, if saw is not in the
# current path, fall back on cabal run saw
SAW=$(shell which saw)
ifeq ($(SAW),)
  ifeq ($(CI),)
	    SAW=cabal run saw
  else
    $(error Could not find SAW executable; PATH = $(PATH))
  endif
endif

generated/CryptolToCoq/SAWCorePrelude.v: ../../saw-core/prelude/Prelude.sawcore
	(cd ../saw; $(SAW) generate_scaffolding.saw)

generated/CryptolToCoq/CryptolPrimitivesForSAWCore.v: ../../cryptol-saw-core/saw/Cryptol.sawcore
	(cd ../saw; $(SAW) generate_scaffolding.saw)
