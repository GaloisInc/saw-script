.PHONY : SAWScript clean

SAWScript : 
	cd SAWScript; make all

REPL : SAWScript
	ghc -o ../bin/saw Main.hs

clean :
	-rm *.o *.hi
	-cd SAWScript; make clean