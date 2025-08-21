all:
	@echo "This makefile is administrative only."
	@echo "To run the tests, do 'cabal test integration-tests'."
	@false

# Regenerate MIR blobs
# (descend into every dir that has one)
regen-mir-blobs:
	@for D in $$(ls */*.linked-mir.json | sed 's,/[^/]*$$,,' | sort -u); do\
		echo "*** regen-mir-blobs in $$D ***"; \
		(cd "$$D" && $(MAKE) regen-mir-blobs); \
	 done

# Remove things left behind by running the tests
# (descend into every dir that has a makefile)
clean:
	@for D in $$(ls */Makefile | sed 's,/[^/]*$$,,' | sort -u); do \
		echo "*** clean in $$D ***"; \
		(cd "$$D" && $(MAKE) clean); \
	 done
