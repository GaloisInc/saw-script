# note: only attempt to regenerate on an x86_64 machine
AS = yasm
ASFLAGS = -felf64
LD = ld
CC = clang
CFLAGS = -O0

all: foo bar.bc

foo: foo.o
	$(LD) foo.o -o $@

foo.o:
	$(AS) $(ASFLAGS) foo.S

bar.bc: bar.c
	$(CC) $(CFLAGS) -c -emit-llvm $< -o $@

clean:
	rm -f foo.o bar.bc

.PHONY: all clean
