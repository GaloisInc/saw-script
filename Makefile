ABC=../../abcBridge
LLVM_PRETTY=../../llvm-pretty

all:
	cabal-dev install . ../Verinf ../Java ../LLVM $(ABC) $(LLVM_PRETTY)

clean:
	cabal clean

saw:
	cd src; make REPL