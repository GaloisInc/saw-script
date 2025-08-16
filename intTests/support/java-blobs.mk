# Make fragment for building Java binary blobs
# Usage:
#    - set JAVA_SRCS to the basenames of all Java sources
#      (e.g. if you have foo.java, set JAVA_SRCS=foo)
#    - set JAVAC to some other javac if necessary
#    - set JAVACFLAGS to other flags if necessary (default is -g)
#    - set SUPPORTDIR if needed (see below)
#    - include this file
#    - make sure some version of "all:" is still the first target (it
#      is first here, but if you include multiple fragments or need
#      other stuff first, put "all:;" at the top of your makefile)
#
# XXX: This does not handle cases where one .java file produces
# XXX: multiple output .class files.
#
# To use this file from outside the intTests tree, set SUPPORTDIR
# explicitly to point at intTests/support. (Notably, this file is
# also used for the saw-python test artefacts.)
SUPPORTDIR?=../support

JAVAC?=javac
JAVACFLAGS?=-g

# Make the output names
JAVA_BLOBS=$(patsubst %, %.class, $(JAVA_SRCS))

# "all" builds all blobs
all: all-java-blobs
all-java-blobs: $(JAVA_BLOBS)

$(JAVA_BLOBS): %.class: %.java
	$(JAVAC) $(JAVACFLAGS) $<
	$(JAVAC) --version |\
		$(SUPPORTDIR)/update-from.sh "$@.FROM"

# "regen" force-rebuilds all blobs.
# Note: explicitly only build the Java blobs we control; if we
# recursively build all and there's multiple kinds of blobs that'll
# build everything, which will blow up if you run in parallel.
regen: regen-java-blobs
regen-java-blobs:
	rm -f $(JAVA_BLOBS)
	$(MAKE) all-java-blobs
	$(MAKE) tidy-java-blobs

# "tidy" (not "clean") cleans up the leftovers we don't keep around
# (there aren't any)
tidy: tidy-java-blobs
tidy-java-blobs: ;

# this is another name we've been using for "tidy"
# ...which in addition to being long has two spellings
remove-unused-build-artifacts: tidy
remove-unused-build-artefacts: tidy

# "destroy" deletes the blobs without rebuilding them
# (there is probably no need to actually have this target)
# also run tidy for tidiness
destroy: destroy-java-blobs
destroy-java-blobs: tidy
	rm -f $(JAVA_BLOBS)

# "clean" does nothing here; just make sure it exists.
# "clean" is for removing test run results, and we don't
# incur any just by having test blobs.
#
# Unfortunately, it looks like we need a dummy rule with an invocation
# of true to keep gmake from getting upset.
clean: clean-java-blobs
clean-java-blobs:
	@true

.PHONY: all all-java-blobs regen regen-java-blobs tidy tidy-java-blobs
.PHONY: remove-unused-build-artifacts
.PHONY: remove-unused-build-artefacts
.PHONY: destroy destroy-java-blobs clean clean-java-blobs

