# This test needs to do its own thing because it compiles one source
# file with different options, which llvm-blobs.mk doesn't support.

CLANG=clang
CFLAGS=

SANITIZE=\
	-fsanitize=unsigned-integer-overflow \
	-fsanitize-trap=unsigned-integer-overflow

BLOBS=add-normal.bc add-sanitized.bc

all: all-blobs
all-blobs: $(BLOBS)

%-normal.bc: %.c
	$(CLANG) $(CFLAGS) -c -emit-llvm -o $@ $<
	$(CLANG) --version |\
		$(SUPPORTDIR)/update-from.sh "$@.FROM"

%-sanitized.bc: %.c
	$(CLANG) $(CFLAGS) $(SANITIZE) -c -emit-llvm -o $@ $<
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
