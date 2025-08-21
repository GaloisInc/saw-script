# Make fragment for building x86 binary blobs from assembly
# Usage:
#    - set X86_SRCS to the basenames of all x86 assembly blob sources
#    - set AS to some other assembler if necessary (default is "yasm")
#    - set ASFLAGS if necessary (default is -felf64)
#    - set LD to some other linker if necessary (default is "ld")
#    - set LDFLAGS if needed (default is empty)
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

AS?=yasm
ASFLAGS?=-felf64
LD?=ld
LDFLAGS?=

# Make the output names
X86_OBJS=$(patsubst %, %.o, $(X86_SRCS))
X86_BINS=$(X86_SRCS)

# We don't need (or want) to keep the .o files
X86_TIDY=$(X86_OBJS)

# "all" builds all blobs
all: all-x86-blobs
all-x86-blobs: $(X86_BINS)

$(X86_BINS): %: %.S
	$(AS) $(ASFLAGS) $<
	$(LD) $(LDFLAGS) $(patsubst, %.S, %.o, $<) -o $@
	($(AS) --version; $(LD) --version) |\
		$(SUPPORTDIR)/update-from.sh "$@.FROM"

# "regen" force-rebuilds all blobs.
# Note: explicitly only build the X86 blobs we control; if we
# recursively build all and there's multiple kinds of blobs that'll
# build everything, which will blow up if you run in parallel.
regen: regen-x86-blobs
regen-x86-blobs:
	rm -f $(X86_BINS)
	$(MAKE) all-x86-blobs
	$(MAKE) tidy-x86-blobs

# "tidy" (not "clean") cleans up the leftovers we don't keep around.
tidy: tidy-x86-blobs
tidy-x86-blobs:
	rm -f $(X86_TIDY)

# this is another name we've been using for "tidy"
# ...which in addition to being long has two spellings
remove-unused-build-artifacts: tidy
remove-unused-build-artefacts: tidy

# "destroy" deletes the blobs without rebuilding them
# (there is probably no need to actually have this target)
# also run tidy for tidiness
destroy: destroy-x86-blobs
destroy-x86-blobs: tidy
	rm -f $(X86_BINS)

# "clean" does nothing here; just make sure it exists.
# "clean" is for removing test run results, and we don't
# incur any just by having test blobs.
#
# Unfortunately, it looks like we need a dummy rule with an invocation
# of true to keep gmake from getting upset.
clean: clean-x86-blobs
clean-x86-blobs:
	@true

.PHONY: all all-x86-blobs regen regen-x86-blobs tidy tidy-x86-blobs
.PHONY: remove-unused-build-artifacts
.PHONY: remove-unused-build-artefacts
.PHONY: destroy destroy-x86-blobs clean clean-x86-blobs
