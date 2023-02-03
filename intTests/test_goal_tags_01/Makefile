.PHONY: all clean

CC ?= clang
CFLAGS ?= -O0 -emit-llvm
SAW ?= saw

all: test.bc
	$(SAW) test.saw

clean:
	rm -f *.bc *.ll *.log

%.bc: %.c
	$(CC) $(CFLAGS) -g -c -o $@ $^

%.ll: %.c
	$(CC) $(CFLAGS) -g -c -S -o $@ $^
