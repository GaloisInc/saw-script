# note: only attempt to regenerate on an x86_64 machine
AS = yasm
ASFLAGS = -felf64
LD = ld
CC = clang
CFLAGS = -O0

all: addvar test.bc

addvar: addvar.o
	$(LD) addvar.o -o $@

addvar.o:
	$(AS) $(ASFLAGS) addvar.S

test.bc: test.c
	$(CC) $(CFLAGS) -c -emit-llvm $< -o $@

clean:
	rm -f addvar.o test.bc

.PHONY: all clean
