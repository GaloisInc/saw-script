.PHONY: all clean regen

CLANGXX ?= clang++
# Force Itanium ABI so that mangled symbol names are stable across platforms.
# (extern "C" entry points avoid the question for the test itself, but using
# a linux target also keeps the bitcode portable.)
TARGET  ?= --target=x86_64-pc-linux-gnu
CXXFLAGS ?= -std=c++17 -O0 -g

all: error-return-value.bc

error-return-value.bc: error-return-value.cpp
	$(CLANGXX) $(TARGET) $(CXXFLAGS) -emit-llvm -c \
	    error-return-value.cpp -o error-return-value.bc
	$(CLANGXX) --version | head -1 > error-return-value.bc.FROM

regen: clean all

clean:
	rm -f error-return-value.bc error-return-value.bc.FROM
