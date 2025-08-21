# note: only attempt to regenerate on an x86_64 machine

LLVM_C_SRCS=test
include ../support/llvm-blobs.mk

# We also want to compile test.c to an executable
all: all-exe
all-exe: test

test: test.c
	$(CLANG) $(CFLAGS) $< -o $@
	$(CLANG) --version |\
		$(SUPPORTDIR)/update-from.sh "$@.FROM"

regen: regen-exe
regen-exe:
	rm -f test
	$(MAKE) test

destroy: destroy-exe
destroy-exe:
	rm -f test

.PHONY: all regen regen-exe destroy destroy-exe
