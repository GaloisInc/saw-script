# Make fragment for building LLVM binary blobs
# Usage:
#    - set LLVM_C_SRCS to the basenames of all C blob sources
#    - set LLVM_RUST_SRCS to the basenames of all Rust blob sources
#      (e.g. if you have foo.c and bar.rs, set LLVM_C_SRCS=foo and
#      LLVM_RUST_SRCS=bar)
#    - set MAKE_LL_FILES=yes if this test checks in *.ll files
#    - set CC to some other clang if necessary
#    - set CFLAGS if necessary (default is -g -O0)
#    - set SUPPORTDIR if needed (see below)
#    - include this file
#    - make sure some version of "all:" is still the first target (it
#      is first here, but if you include multiple fragments or need
#      other stuff first, put "all:;" at the top of your makefile)
#
# To use this file from outside the intTests tree, set SUPPORTDIR
# explicitly to point at intTests/support. (Notably, this file is
# also used for the saw-python test artefacts.)
SUPPORTDIR?=../support

CLANG?=clang
CFLAGS?=-g -O0

# Make the output names
LLVM_C_BITCODE=$(patsubst %, %.bc, $(LLVM_C_SRCS))
LLVM_C_LL=$(patsubst %, %.ll, $(LLVM_C_SRCS))
LLVM_RUST_BITCODE=$(patsubst %, %.bc, $(LLVM_RUST_SRCS))
LLVM_RUST_LL=$(patsubst %, %.ll, $(LLVM_RUST_SRCS))

LLVM_BLOBS=$(LLVM_C_BITCODE) $(LLVM_RUST_BITCODE)
# If MAKE_LL_FILES is set, treat the .ll files as blobs we want.
ifeq ($(MAKE_LL_FILES), yes)
LLVM_BLOBS+=$(LLVM_C_LL) $(LLVM_RUST_LL)
endif

# "all" builds all blobs
all: all-llvm-blobs
all-llvm-blobs: $(LLVM_BLOBS)
	$(MAKE) tidy-llvm-blobs

$(LLVM_C_BITCODE): %.bc: %.c
	$(CLANG) $(CFLAGS) -c -emit-llvm $< -o $@
	$(CLANG) --version |\
		$(SUPPORTDIR)/update-from.sh "$@.FROM"

$(LLVM_C_LL): %.ll: %.c
	$(CLANG) $(CFLAGS) -S -emit-llvm $< -o $@
	$(CLANG) --version |\
		$(SUPPORTDIR)/update-from.sh "$@.FROM"

$(LLVM_RUST_BITCODE): %.bc: %.rs
	rustc --emit=llvm-ir $(patsubst %.bc, %.rs, $@)
	llvm-as $(patsubst %.bc, %.ll, $@)
	(rustc --version; llvm-as --version) |\
		$(SUPPORTDIR)/update-from.sh "$@.FROM"
ifeq ($(MAKE_LL_FILES), yes)
	(rustc --version; llvm-as --version) |\
		$(SUPPORTDIR)/update-from.sh "$(patsubst %.bc, %ll, $@).FROM"
else
	rm -f $(patsubst %.bc, %ll, $@)
endif

# "regen" force-rebuilds all blobs.
# Note: explicitly only build the LLVM blobs we control; if we
# recursively build all and there's multiple kinds of blobs that'll
# build everything, which will blow up if you run in parallel.
regen: regen-llvm-blobs
regen-llvm-blobs:
	rm -f $(LLVM_BLOBS)
	$(MAKE) all-llvm-blobs
	$(MAKE) tidy-llvm-blobs

# "tidy" (not "clean") cleans up the leftovers we don't keep around.
tidy: tidy-llvm-blobs
tidy-llvm-blobs: ;

# this is another name we've been using for "tidy"
# ...which in addition to being long has two spellings
remove-unused-build-artifacts: tidy
remove-unused-build-artefacts: tidy

# "destroy" deletes the blobs without rebuilding them
# (there is probably no need to actually have this target)
# also run tidy for tidiness
destroy: destroy-llvm-blobs
destroy-llvm-blobs: tidy
	rm -f $(LLVM_BLOBS)

# "clean" does nothing here; just make sure it exists.
# "clean" is for removing test run results, and we don't
# incur any just by having test blobs.
#
# Unfortunately, it looks like we need a dummy rule with an invocation
# of true to keep gmake from getting upset.
clean: clean-llvm-blobs
clean-llvm-blobs:
	@true

.PHONY: all all-llvm-blobs regen regen-llvm-blobs tidy tidy-llvm-blobs
.PHONY: remove-unused-build-artifacts
.PHONY: remove-unused-build-artefacts
.PHONY: destroy destroy-llvm-blobs clean clean-llvm-blobs
