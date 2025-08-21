CP=.:../jars/galois.jar

SRCS=FFS Id
JAVACFLAGS=-cp $(CP)
include ../support/java-blobs.mk

# This test also checks in .jvm-asm files, so build those.
ASMS=$(patsubst %, %.jvm-asm, $(SRCS))
all: all-asm-files
all-asm-files: $(ASMS)

$(ASMS): %.jvm-asm: %.java
	javap -c -classpath $(CP) $(patsubst %.java, %, $<) > $@
	javap -version |\
		$(SUPPORTDIR)/update-from.sh "$@.FROM"

regen: regen-asm-files
regen-asm-files:
	rm -f $(ASMS)
	$(MAKE) all-asm-files

destroy: destroy-asm-files
destroy-asm-files:
	rm -f $(ASMS)

.PHONY: all all-asm-files regen regen-asm-files
.PHONY: destroy destroy-asm-files
