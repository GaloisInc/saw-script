# note: only attempt to regenerate on an x86_64 machine

LLVM_C_SRCS=test
include ../support/llvm-blobs.mk

# We also want to compile test.c to an executable, which is
# called test.exe
all: all-exe
all-exe: test.exe

test.exe: test.c
	$(CLANG) $(CFLAGS) $< -o $@
	$(CLANG) --version |\
		$(SUPPORTDIR)/update-from.sh "$@.FROM"

regen: regen-exe
regen-exe:
	rm -f test.exe
	$(MAKE) all-exe

destroy: destroy-exe
destroy-exe:
	rm -f test.exe

.PHONY: all regen regen-exe destroy destroy-exe
