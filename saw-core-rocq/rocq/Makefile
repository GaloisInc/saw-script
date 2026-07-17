all: Makefile.rocq

Makefile.rocq: _RocqProject
	rocq makefile -f $< -o $@

include Makefile.rocq

# If not in CI, find a SAW executable. (In CI, "saw" should always be
# on the path. If it's not, something's wrong and we should let it
# fail.
#
# Try actually running it to be sure.
SAW=saw
ifeq ($(CI),)
  OK=$(shell $(SAW) -h 2>&1 | grep solver-cache >/dev/null && echo OK)
  ifeq ($(OK),)
    # The command line handling of "cabal run" does not conform to
    # usual expectations. Plain words after exe:saw are interpreted as
    # arguments for saw, but options as options for Cabal. The --
    # tells cabal to stop looking for options. We also need -v0 to
    # keep it from mixing its own output with SAW's.
    SAW=cabal run -v0 exe:saw --
    OK=$(shell $(SAW) -h 2>&1 | grep solver-cache >/dev/null && echo OK)
    ifeq ($(OK),)
      $(error Could not find SAW (including via cabal); PATH=$(PATH))
    endif
  endif
endif

generated/CryptolToRocq/SAWCorePrelude.v: ../../saw-core/prelude/Prelude.sawcore
	(mkdir -p generated/CryptolToRocq && cd ../saw && $(SAW) generate_scaffolding.saw)

generated/CryptolToRocq/CryptolPrimitivesForSAWCore.v: ../../cryptol-saw-core/saw/Cryptol.sawcore
	(mkdir -p generated/CryptolToRocq && cd ../saw && $(SAW) generate_scaffolding.saw)
