# note: only attempt to regenerate on an x86_64 machine
AS = yasm
ASFLAGS = -felf64
LD = ld
CC = clang
CFLAGS = -O0

all: precondtest test.bc

precondtest: precondtest.o
	$(LD) precondtest.o -o $@

precondtest.o:
	$(AS) $(ASFLAGS) precondtest.S

test.bc: test.c
	$(CC) $(CFLAGS) -c -emit-llvm $< -o $@

clean:
	rm -f precondtest.o test.bc

.PHONY: all clean
