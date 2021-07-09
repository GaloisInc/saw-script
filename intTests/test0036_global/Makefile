CC = clang
CFLAGS = -g -emit-llvm -frecord-command-line
OUTPUT_FILES = test-O1.bc test-O2.bc test-O1.ll test-O2.ll

all: $(OUTPUT_FILES)

test-O1.bc : test.c
	$(CC) $(CFLAGS) -O1 -c $< -o $@
test-O1.ll : test.c
	$(CC) $(CFLAGS) -O1 -S $< -o $@
test-O2.bc : test.c
	$(CC) $(CFLAGS) -O2 -c $< -o $@
test-O2.ll : test.c
	$(CC) $(CFLAGS) -O2 -S $< -o $@

.PHONY: clean
clean:
	rm -f $(OUTPUT_FILES)
