# Make fragment for building mir-json binary blobs
# Usage:
#    - set MIR_SRCS to the basenames of all Rust sources
#      (e.g. if you have foo.rs and bar.rs, set MIR_SRCS=foo bar)
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

# Make the output names
MIR_BLOBS=$(patsubst %, %.linked-mir.json, $(MIR_SRCS))

# Building foo.linked-mir.json from foo.rs also produces:
#    foo
#    libfoo.mir
#    libfoo.rlib
# In these filenames rustc also quietly replaces any - with a _.
# Note that the $(subst) invocation must have a space before the
# dash (or it doesn't work) but _not_ before the underscore (or
# it inserts spaces in the output and fails). Yay gmake :-(
#
MIR_TIDY_PROGS=$(MIR_SRCS)
MIR_TIDY_MIR=$(subst -,_, $(patsubst %, lib%.mir, $(MIR_SRCS)))
MIR_TIDY_RLIB=$(subst -,_, $(patsubst %, lib%.rlib, $(MIR_SRCS)))
MIR_TIDY=$(MIR_TIDY_PROGS) $(MIR_TIDY_MIR) $(MIR_TIDY_RLIB)

# "all" builds all blobs
all: all-mir-blobs
all-mir-blobs: $(MIR_BLOBS)
	$(MAKE) tidy-mir-blobs

$(MIR_BLOBS): %.linked-mir.json: %.rs
	saw-rustc $<
	$(SUPPORTDIR)/identify-mir-json.sh |\
		$(SUPPORTDIR)/update-from.sh "$@.FROM"

# "regen" force-rebuilds all blobs.
# Note: explicitly only build the MIR blobs we control; if we
# recursively build all and there's multiple kinds of blobs that'll
# build everything, which will blow up if you run in parallel.
regen: regen-mir-blobs
regen-mir-blobs:
	rm -f $(MIR_BLOBS)
	$(MAKE) all-mir-blobs
	$(MAKE) tidy-mir-blobs

# "tidy" (not "clean") cleans up the leftovers we don't keep around
tidy: tidy-mir-blobs
tidy-mir-blobs:
	rm -f $(MIR_TIDY)

# this is another name we've been using for "tidy"
# ...which in addition to being long has two spellings
remove-unused-build-artifacts: tidy
remove-unused-build-artefacts: tidy

# "destroy" deletes the blobs without rebuilding them
# (there is probably no need to actually have this target)
# also run tidy for tidiness
destroy: destroy-mir-blobs
destroy-mir-blobs: tidy
	rm -f $(MIR_BLOBS)

# "clean" does nothing here; just make sure it exists.
# "clean" is for removing test run results, and we don't
# incur any just by having test blobs.
#
# Unfortunately, it looks like we need a dummy rule with an invocation
# of true to keep gmake from getting upset.
clean: clean-mir-blobs
clean-mir-blobs:
	@true

.PHONY: all all-mir-blobs regen regen-mir-blobs tidy tidy-mir-blobs
.PHONY: remove-unused-build-artifacts
.PHONY: remove-unused-build-artefacts
.PHONY: destroy destroy-mir-blobs clean clean-mir-blobs
