# note: only attempt to regenerate on an x86_64 machine
AS = yasm
ASFLAGS = -felf64
LD = ld
CC = clang
CFLAGS = -O0

all: returntest test.bc

returntest: returntest.o
	$(LD) returntest.o -o $@

returntest.o:
	$(AS) $(ASFLAGS) returntest.S

test.bc: test.c
	$(CC) $(CFLAGS) -c -emit-llvm $< -o $@

clean:
	rm -f returntest.o test.bc

.PHONY: all clean
