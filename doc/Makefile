# SAW Documentation Makefile
# This is derived from Sphinx's default Makefile
include .env

SPHINXOPTS    ?=
SPHINXBUILD   ?= sphinx-build
SOURCEDIR     = .
BUILDDIR      = _build

SUPPORTED_DOCS = html latex latexpdf linkcheck

help:
	$(info SAW Documentation (based on Sphinx))
	$(info Setup Python environment: 'make setup-env')
	$(info Package code samples: 'make package-code')
	$(info Supported document formats: 'make' + one of: $(SUPPORTED_DOCS))
	$(info Install PDFs to repository: 'make install-pdf')
	$(info Tidy code packages / docs: 'make mostlyclean')
	$(info Tidy everything, including Python venv: 'make clean')

sphinx-help: setup-env
	@. .venv/bin/activate && $(SPHINXBUILD) -M help "$(SOURCEDIR)" "$(BUILDDIR)" $(SPHINXOPTS) $(O)

.PHONY: setup-env package-code pdf install-pdf mostlyclean clean help $(SUPPORTED_DOCS)

setup-env:
	scripts/setup_env.sh

package-code:
	scripts/package_code.sh

pdf: latexpdf

install-pdf: latexpdf
	mkdir -p pdfs
	cp -f $$(ls _build/latex/*.pdf | sed '/\/galois\.pdf$$/d') pdfs

mostlyclean:
	rm -rf _build
	rm -rf **/code.tar.gz

clean: mostlyclean
	rm -rf .venv

$(SUPPORTED_DOCS): package-code setup-env
	@SOURCE_DATE_EPOCH=${SOURCE_DATE_EPOCH} . .venv/bin/activate && $(SPHINXBUILD) -M $@ "$(SOURCEDIR)" "$(BUILDDIR)" $(SPHINXOPTS) $(O)

%:
	$(error "Target '$@' unknown; try 'make help'.")
