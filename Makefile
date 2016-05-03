# Make Emacs-format tags.
.PHONY: tmp/TAGS
tmp/TAGS: | tmp
	hasktags --ignore-close-implementation --etags --tags-absolute --output=tmp/TAGS src deps/*/src

tmp:
	mkdir -p tmp
