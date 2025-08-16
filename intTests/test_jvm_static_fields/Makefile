# This can't use java-blobs.mk because it generates three .class
# files, none of them named after the .java file, and gmake doesn't
# have what it takes to abstract that.

# B.class and C.class will come along for the ride
all: A.class

A.class: Test.java
	javac -g Test.java
	$(JAVAC) --version |\
		$(SUPPORTDIR)/update-from.sh "$@.FROM"
	cp A.class.FROM B.class.FROM
	cp A.class.FROM C.class.FROM

# "regen" force-rebuilds all blobs.
regen:
	rm -f *.class
	$(MAKE) all
	$(MAKE) tidy

# "tidy" (not "clean") cleans up the leftovers we don't keep around
# (there aren't any)
tidy: ;
remove-unused-build-artifacts: tidy
remove-unused-build-artefacts: tidy

# "destroy" deletes the blobs without rebuilding them
# (there is probably no need to actually have this target)
# also run tidy for tidiness
destroy:
	rm -f *.class

# "clean" does nothing here; just make sure it exists.
# "clean" is for removing test run results, and we don't
# incur any just by having test blobs.
clean:
	@true

.PHONY: all regen tidy destroy clean
.PHONY: remove-unused-build-artifacts
.PHONY: remove-unused-build-artefacts
