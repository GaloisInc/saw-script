ABC=../../abcBridge
LLVM_PRETTY=../../llvm-pretty

all:
	cabal-dev install . ../Verinf ../Java ../LLVM ../SAWCore $(ABC) $(LLVM_PRETTY)

clean:
	cabal clean
