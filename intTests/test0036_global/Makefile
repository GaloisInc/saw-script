# This test needs to do its own thing because it compiles one source
# file with different options, which llvm-blobs.mk doesn't support.

CLANG=clang

CFLAGS.test-O1=-g -O1
CFLAGS.test-O2=-g -O2
CFLAGS.test-signed=-g -O0

BLOBS=test-O1.bc test-O2.bc test-O1.ll test-O2.ll test-signed.bc

all: all-blobs
all-blobs: $(BLOBS)

%.bc: test.c
	$(CLANG) $(CFLAGS.$(patsubst %.bc, %, $@)) -c -emit-llvm test.c -o $@
	$(CLANG) --version |\
		$(SUPPORTDIR)/update-from.sh "$@.FROM"

%.ll: test.c
	$(CLANG) $(CFLAGS.$(patsubst %.ll, %, $@)) -S -emit-llvm test.c -o $@
	$(CLANG) --version |\
		$(SUPPORTDIR)/update-from.sh "$@.FROM"

regen: regen-blobs
regen-blobs:
	rm -f $(BLOBS)
	$(MAKE) all-blobs

tidy: ;
remove-unused-build-artifacts: tidy
remove-unused-build-artefacts: tidy

destroy: destroy-blobs
destroy-blobs:
	rm -f $(BLOBS)

clean:
	@true

.PHONY: all all-blobs regen regen-blobs tidy
.PHONY: remove-unused-build-artifacts
.PHONY: remove-unused-build-artefacts
.PHONY: destroy destroy-blobs clean
