# SAW Documentation

Welcome to the home of all things SAW documentation!

This `README` covers:

- Building the documentation
- The structure of `doc/` (this directory), including how to add new materials
- Information for developers working on the Sphinx build itself, and not just
  documentation content

## Building the documentation

For the sake of rapid editing and simple deployment, we have attempted to make
it as easy as possible to build SAW's documentation, especially for those only
interested in modifying the documentation _content_.

### Prerequisites

The only _strict_ requirement to build the documentation locally is a relatively
recent Python (>=3.9, to be safe - we aren't prioritizing making this work on
every Python under the sun).

This is enough to generate the HTML versions of documentation, which is what is
deployed to <https://galoisinc.github.io/saw-script>.

If you want to generate the PDFs that can be found in `doc/pdfs`, you'll also
need `xelatex`.
This will require a suitable TeX distribution.

### `make_docs.sh`

`doc/make_docs.sh` is a bash script wrapping up all of the Python environment
and Sphinx build management, via [a separately-runnable script we
provide](#the-python-environment).
Using this, you'll almost never need to think about anything related to the
Python behind the curtain, as long as you have a Python >=3.9 installation.

```console
$ ./make_docs.sh
Usage: ./make_docs.sh <html|latexpdf|clean>
```

Running the script with a documentation format does exactly what you expect:
A suitable Python environment is created, any probable code examples are
packaged (see [below](#code-examples)), and the actual Sphinx build is run.

For the `latexpdf` target, in addition to the above, the
[generated PDFs](#pdf-generation) are copied to `pdfs/` so they can be committed
if necessary.

The `clean` target wipes out the Sphinx outputs, as well as any code example
archives that were generated.

#### `setup_env.sh`

There is another script, `setup_env.sh`, that specifically handles the creation
and validation of a suitable Python environment without building the
documentation / code examples.

You can run this separately from `make_docs.sh` if you'd like.

### Troubleshooting

1. If the build succeeds, but you aren't seeing all of the expected changes:

   Try running `./make_docs.sh clean` before rebuilding; Sphinx may have failed
   to detect the changes you made, and you're seeing stale/cached output.
2. If you have unresolved reference warnings:

   Sphinx has an incredibly robust cross-reference system, but it is easy to
   get "wrong".
   If using Markdown/MyST, make sure you are using references according to [this
   documentation](https://myst-parser.readthedocs.io/en/latest/syntax/cross-referencing.html).
3. If the build fails:

   Try removing the `.venv/` directory, forcing a fresh Python environment to be
   created the next time you run `./make_docs.sh ...` or `./setup_env.sh`.

If you still have trouble, you've likely uncovered a bug in the system.
Please [open an issue](https://github.com/GaloisInc/saw-script/issues) detailing
the expected behavior, the observed behavior, and instructions to reproduce the
observed behavior.

## Understanding `doc/`

This directory is the intended source root for all SAW documentation.

### Contents

- The `Makefile` and `conf.py` come from Sphinx; the former is the default one
  gets when starting a new Sphinx project, the latter has been heavily
  customized for SAW's needs.

- `requirements.txt` captures a working set of Python dependencies in an attempt
  to make documentation builds more reproducible.

- `index.md` defines the top-level document hierarchy, and is the intended home
  page of <https://galoisinc.github.io/saw-script>.

- The `bibliography/` directory contains BibTeX (and possibly other)
  bibliographies.

- The `developer/` directory is an assortment of documentation mostly relevant
  to developers of `saw-script`, including:

  - Documentation of the SAWCore `extcore` format
  - Limitations of SAW and its use
  - The `saw-script` release process


- The `figures/` directory is used to store image files / similar resources used
  throughout SAW documentation.

- The `pdfs/` directory is where committed versions of PDF renderings live.
  This may eventually be removed in favor of generating and distrubiting PDFs as
  part of CI.

- `saw-lexer` is a small Python package implementing a SAWScript `pygments`
  lexer, so our documentation understands and properly renders fenced code
  blocks labeled ```````sawscript````.

The remaining directories correspond to individual SAW documentation resources
currently managed as part of this documentation ecosystem:

- `llvm-java-verification-with-saw/`
  "LLVM/Java Verification with SAW"
  This is a tutorial-style introduction to SAW
- `rust-verification-with-saw/`
  "Rust Verification with SAW"
  Like the above, but using the experimental MIR features
- `saw-user-manual/`
  "SAW User Manual"
  The only 'complete' SAW reference right now

### Non-contents

These are pieces of documentation in `saw-script` that are _not_ part of the
`doc/` ecosystem:

- `saw-core/doc/`: A lone TeX file, presumably describing formalism related to
  the SAWCore intermediate representation
- `saw-remote-api/docs/`: An old Sphinx setup for SAW's Python remote API

### Adding new materials

Sphinx provides a great deal of flexibility, but we prefer to keep that
flexibility in check by maintaining a close correspondence between the directory
structure of `doc/` and the document hierarchy its contents define.

That said, to add new documentation material:

1. Create a new directory in `doc/` for your material.
   Name it the same as your intended title, or an appropriate transformation (to
   e.g. remove spaces/spcial characters).

   Add an `index.md` file that will define the top-level of your material's
   hierarchy with a `toctree`.
   Feel free to make this `toctree` `:hidden:`, give it a `:caption:`, or make
   any other decisions appropriate for your material.
   As long as the `toctree` is defined, even if it is hidden Sphinx will do the
   right thing to generate HTML/PDFs.

   Do note that, for materials intended to add to `doc/pdfs/`, the contents of
   their `index.md` (other than the hierarchical information) will **not**
   render in the PDF - this is an intentional choice to allow for some
   "HTML-only" content in the front-matter (e.g. code downloads for tutorials).
   See [below](#pdf-generation) for information about setting the title of
   generated PDFs given this rendering quirk.
2. Create additional `.md` files for your content, organizing them using
   `toctree`s as appropriate.
   Ideally, for every entry in the top-level `toctree` of your material, there
   will be a corresponding `.md` file (or directory of `.md` files, possibly
   with its own `index.md` and additional `toctree`s).
   This is how we maintain the directory structure / document hierarchy
   correspondence.

Note that your documentation doesn't necessarily _need_ its own directory; if
it's a single page, consider adding it as a single `.md` file to the most
appropriate directory, and adding an entry to the corresponding `toctree` (for
some examples of this, see `doc/developer/`).

#### Code examples

It is useful to provide code sample downloads when writing tutorial-style
documentation materials, so readers can easily follow along.

When building with the `make_docs.sh` helper script, `doc/` is set up to easily
allow code samples to be added anywhere they are needed.

Note that this works best for materials that have their own dedicated directory:
If you are adding a document to a directory already containing code samples,
you'll need to determine whether it is appropriate to reorganize your document
so it can have its own downloadable code, or add to the code samples already
provided.

To add code samples to your own material:

1. Taking the note above into consideration, find/create the appropriate `code/`
   directory.
2. Add your code/other materials to include in the package to it.
3. When you need to add a download link for the directory, use the path to the
   `code/` directory, but add `.tar.gz`.
   For example, if you've added `doc/my-cool-saw-tutorial` with code in
   `doc/my-cool-saw-tutorial/code`, if you want to add a download link in
   `doc/my-cool-saw-tutorial/index.md` you would write:

   ```markdown
   Download sample files: <path:code.tar.gz>
   ```

**Important!** This convenience is **not** a built-in Sphinx feature, but a
feature provided by our higher-level `make_docs.sh` wrapper.
If you want to use Sphinx to build directly (e.g. with `make`), you will need
to generate the `code.tar.gz` files yourself, which will _not_ be validated as
'true' archives of the sibling `code/` directories.
For this reason, we strongly recommend that you _always_ build SAW documentation
using the helper scripts.

#### PDF generation

Some resources should be turned into PDFs stored in `doc/pdfs`.

Fortunately, Sphinx allows for the layout of generated TeX / PDFs to be
controlled at a fairly granular level.
The file `doc/conf.py` attempts to simplify this for our purposes.

In that configuration, there is a variable `pdfs` that holds a reference to a
list of 3-tuples of strings, each of which has the following form:

`(<document root directory name>, <document title>, "howto"|"manual")`

The first entry is the root of the resource, assumed to contain an `index.md`
document defining the `toctree` for the resource.

The second entry is the title as it will render on the PDF cover page.

The third entry essentially determines the top-level layout of the material:
`"howto"` results in sections at the top-level, while `"manual"` results in
chapters.
It's a good idea to play with both to find the right fit for your documentation.

By adding an entry to the `pdfs` list, Sphinx will build a TeX document and
corresonding PDF rooted at the configured directory.
This is indeed how we generate the separate tutorials and user manual, even
though `doc/` is _technically_ one giant document.

If you need to use this feature, consult `doc/conf.py` for additional
documentation (and to see the tutorials/manual example configurations).

## For developers

These notes are primarily for those developers working on the documentation
ecosystem itself.

### Sphinx doesn't _require_ Markdown

Because all of the existing SAW documentation was authored in (variants of)
Markdown, it was convenient to use extensions (i.e. `myst-parser`) to quickly
move the existing work into a Sphinx environment without having to translate to
restructuredText.

This is because Sphinx is a documentation _engine_, capable of handling all
kinds of inputs (and producing all kinds of outputs).
In this way, it is similar to the `pandoc` approach we took previously.

That said, due to this flexibility, it is possible to mix-and-match reST and
Markdown when authoring documentation - Sphinx will take care of properly parsing
and resolving everything.

We **strongly** recommend that you stick with Markdown (and the extensions
provided by MyST) unless strictly necessary when authoring SAW documentation,
for consistency with existing materials and to avoid issues resolving, for
example, heading levels.

### The Python environment

If you are hacking on the documentation build itself (e.g. configuring Sphinx,
playing with new extensions, or even simply upgrading the pinned dependencies in
<./requirements.txt>), you can manually activate the Python virtual environment
with `.venv/bin/activate`, and deactivate it again with `deactivate`.

This ought not be necessary for most work on documentation.
