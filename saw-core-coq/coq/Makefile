all: Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f $< -o $@

include Makefile.coq

# Set the SAW variable to the appropriate command. Always look in the path
# first, otherwise fall back on cabal run saw, unless running in CI because if
# saw is not in the path in CI then something else is terribly wrong and that
# should be an error
SAW=$(shell which saw)
ifeq ($(SAW),)
  ifeq ($(CI),)
	    SAW=cabal run exe:saw
  else
    $(error Could not find SAW executable; PATH = $(PATH))
  endif
endif

generated/CryptolToCoq/SAWCorePrelude.v: ../../saw-core/prelude/Prelude.sawcore
	(mkdir -p generated/CryptolToCoq; cd ../saw; $(SAW) generate_scaffolding.saw)

generated/CryptolToCoq/CryptolPrimitivesForSAWCore.v: ../../cryptol-saw-core/saw/Cryptol.sawcore
	(mkdir -p generated/CryptolToCoq; cd ../saw; $(SAW) generate_scaffolding.saw)
