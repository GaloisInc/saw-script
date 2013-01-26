.PHONY: clean

GHC_OPTS = -no-user-package-db -package-db cabal-dev/packages-7.6.1.conf

test : Main.hs SAWScript/*.hs SAWScript/Unify/*.hs SAWScript/Lexer.x SAWScript/Parser.y
	$(MAKE) -C SAWScript
	@echo
	ghc ${GHC_OPTS} -o test Main.hs

clean :
	$(MAKE) -C SAWScript clean
	@echo
	rm -f *.o *.hi test

