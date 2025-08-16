# note: only attempt to regenerate on an x86_64 machine
AS = yasm
ASFLAGS = -felf64
LD = ld
CC = clang
CFLAGS = -O0

all: increment test.bc

increment: increment.o
	$(LD) increment.o -o $@

increment.o:
	$(AS) $(ASFLAGS) increment.S

test.bc: test.c
	$(CC) $(CFLAGS) -c -emit-llvm $< -o $@

clean:
	rm -f increment.o test.bc

.PHONY: all clean
