ROCQDIR=../../saw-core-rocq/rocq

ROCQ=rocq
ROCQFLAGS=\
	-Q $(ROCQDIR)/generated/CryptolToRocq   CryptolToRocq \
	-Q $(ROCQDIR)/handwritten/CryptolToRocq CryptolToRocq

# Note: to load one of these into rocqide, you can do
#    rocqide -f ../../saw-core-rocq/rocq/_RocqProject file.v
#
# However, for either that or the "make rocq" build you must first
# build saw-core-rocq/rocq.

all:
	sh ./test.sh
clean:
	sh ./test.sh clean
	rm -f *.vo *.vo.diff

rocq:
	for f in *.v; do $(MAKE) $${f%.v}.vo || exit 1; done
	cat *.vo.diff
	cat *.vo.diff | awk '{ print "Unexpected test diffs"; exit (1); }'

%.vo: %.v
	$(ROCQ) c $(ROCQFLAGS) $< >$@.log 2>&1 || echo FAILED >> $@.log
	diff -u $@.log.good $@.log > $@.diff || true

rocqdepend:
	$(ROCQ) dep $(ROCQFLAGS) *.v > .depend

-include .depend

.PHONY: all clean rocq
