TARGET   = tmp/sawScriptRustTutorial
SRCS     = ${TARGET}.md ${wildcard *.bib} ${wildcard *.cls} ${wildcard *.sty}
CODE     = ${wildcard code/*.c} \
           ${wildcard code/*.cry} \
           ${wildcard code/*.java} \
           ${wildcard code/*.saw}
TARBALL  = tmp/saw-rust-tutorial-code.tar.gz
SPELLSRC = ${TARGET}.tex
NEWSPELL = ${TARGET}.SPELLNEW
OLDSPELL = ${TARGET}.SPELLOLD
SPELL    = aspell -t -l
AUX      = ${wildcard *.blg} ${wildcard *.bbl} ${wildcard *.aux} \
           ${wildcard *.eps} ${wildcard *.log} ${wildcard *.toc} \
           ${TARGET}.md
PDFARGS   = -H rust-tutorial-head.tex \
            -B rust-tutorial-before.tex \
            -A rust-tutorial-after.tex \
            --toc \
            --listings \
            -V documentclass:galois-whitepaper \
            -V fontsize:12 \
            --pdf-engine=xelatex
HTMLARGS  = --css doc.css \
            -B rust-tutorial-before.html \
	    --toc \
            --standalone \
            --metadata title="SAWScript Rust Tutorial" \
            --self-contained

all: ${TARGET}.pdf ${TARGET}.html ${TARBALL}

${TARGET}.pdf: ${SRCS} Makefile | tmp
	pandoc ${PDFARGS} -o $@ ${TARGET}.md

${TARGET}.html: ${SRCS} Makefile | tmp
	pandoc ${HTMLARGS} -o $@ ${TARGET}.md

${TARBALL}: ${CODE}
	tar czf ${TARBALL} code

# Pre-processing step. Right now, does nothing.
${TARGET}.md: rust-tutorial.md docode.hs ${CODE} | tmp
	runhaskell docode.hs < $< > $@

docode: ${TARGET}.md | tmp

.PHONY: spellClean superClean clean quickSpell

tmp:
	mkdir -p tmp

clean:
	-rm -f ${AUX}

superClean: clean
	-rm -f ${TARGET}.pdf ${TARGET}.html ${TARGET}.md tmp

spellClean:
	rm -f ${NEWSPELL} ${OLDSPELL}

quickSpell:
	@touch ${NEWSPELL}
	@mv -f ${NEWSPELL} ${OLDSPELL}
	@cat ${SPELLSRC} | ${SPELL} | tr "A-Z" "a-z" | sort | uniq | less > ${NEWSPELL}
	@echo '(The ones marked with < are new.)'
	@diff ${NEWSPELL} ${OLDSPELL}
