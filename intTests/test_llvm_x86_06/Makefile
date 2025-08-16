# note: only attempt to regenerate on an x86_64 machine
AS = yasm
ASFLAGS = -felf64
LD = ld
CC = clang
CFLAGS = -O0

all: discoverytest test.bc

discoverytest: discoverytest.o
	$(LD) discoverytest.o -o $@

discoverytest.o:
	$(AS) $(ASFLAGS) discoverytest.S

test.bc: test.c
	$(CC) $(CFLAGS) -c -emit-llvm $< -o $@

clean:
	rm -f discoverytest.o test.bc

.PHONY: all clean
