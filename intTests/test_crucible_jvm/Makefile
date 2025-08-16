JAVA_SRCS=Arr Dyn FFS Iface Obj Stat Sub TestStr
include ../support/java-blobs.mk

# Dyn uses Iface and Arr/Sub use Dyn, so we need to make sure Iface
# and Dyn get explicitly recompiled first; otherwise javac will
# recompile them on its own, and then latter will also recompile the
# former and then we'll get a new class file without updated provenance
# info.
#
# XXX: there should be a make depend to extract this information, but
# putting together the infrastructure to depend Java files is not
# worth it just for this test.
Dyn.class: Iface.class
Arr.class: Dyn.class
Sub.class: Dyn.class

# There's an additional class Foo that comes from TestStr.java. Hack
# a rule for its provenance info. Building TestStr.class will cause it
# to exist; the provenance info should always be the same as
# TestStr's.
all-java-blobs: Foo.class.FROM
Foo.class.FROM: TestStr.class.FROM
	cp TestStr.class.FROM Foo.class.FROM

.PHONY: all-java-blobs
