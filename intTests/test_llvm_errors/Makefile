# The current checked-in foo.bc was generated by:
#    Apple clang version 15.0.0 (clang-1500.1.0.2.5)
#    Target: arm64-apple-darwin22.6.0
#    Thread model: posix
#    InstalledDir: /Library/Developer/CommandLineTools/usr/bin
# but neither the target nor the clang/llvm version is expected to be
# significant.
CC = clang
CFLAGS = -g -O0

all: foo.bc

foo.bc: foo.c
	$(CC) $(CFLAGS) -c -emit-llvm $< -o $@

.PHONY: clean
clean:
	rm -f foo.bc
