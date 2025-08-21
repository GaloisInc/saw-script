# Build
#   - test_switch.bc from test_switch.ll
#   - test_switch2.bc from test_switch2.c
#   - test_switch3.bc from test_switch3.ll
#
# The .ll files are not blobs, they're hand-written or at least hand-tweaked.
#
# XXX: test_switch.ll was removed in 2019, w/o explanation, and possibly
# XXX: by mistake, in commit 7ce7259e9587b51252e1be264d96495521b07a38.
# XXX: Should it be brought back?)

CLANG=clang
CFLAGS=
AS=llvm-as

LLVM_C_SRCS=test_switch2
LLVM_LL_SRCS=test_switch test_switch3

LLVM_C_BITCODE=$(patsubst %, %.bc, $(LLVM_C_SRCS))
LLVM_LL_BITCODE=$(patsubst %, %.bc, $(LLVM_LL_SRCS))
BLOBS=$(LLVM_C_BITCODE) $(LLVM_LL_BITCODE)

all: all-blobs
all-blobs: $(BLOBS)

$(LLVM_C_BITCODE): %.bc: %.c
	$(CLANG) $(CFLAGS) -c -emit-llvm -o $@ $<
	$(CLANG) --version |\
		$(SUPPORTDIR)/update-from.sh "$@.FROM"

$(LLVM_LL_BITCODE): %.bc: %.ll
	llvm-as $<
	llvm-as --version |\
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
