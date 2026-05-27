.PHONY: all clean regen

CLANG  ?= clang
# Pin the target so layout/triple are reproducible across host platforms.
# (Linux SysV is what the committed bitcode was built against.)
TARGET ?= --target=x86_64-pc-linux-gnu
CFLAGS ?= -std=c11 -O0 -g

all: error-return-value.bc

error-return-value.bc: error-return-value.c
	$(CLANG) $(TARGET) $(CFLAGS) -emit-llvm -c \
	    error-return-value.c -o error-return-value.bc
	$(CLANG) --version | head -1 > error-return-value.bc.FROM

regen: clean all

clean:
	rm -f error-return-value.bc error-return-value.bc.FROM
