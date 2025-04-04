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
every Python under the sun), and `make`.

This is enough to generate the HTML versions of documentation, which is what is
deployed to <https://galoisinc.github.io/saw-script>.

If you want to generate the PDFs that can be found in `doc/pdfs`, you'll also
need `xelatex`.
This will require a suitable TeX distribution.

Note that the build will create a Python virtual environment and download the
necessary dependencies via `pip` (see `doc/scripts/requirements.txt`).
You can explicitly run this step with `make setup-env`.

### `Makefile`

As is typical for Sphinx projects, SAW's documentation is built using `make`.

Our `Makefile` is a tailored version of that which is generated when starting a
new Sphinx project, in particular restricting the document formats that can be
targeted, and handling the setup of an appropriate Python environment in which
to run the Sphinx build.

Typing `make help` is the easiest way to get started.
The following targets are available:

- `help`: Display all of the most useful targets
- `sphinx-help`: Display Sphinx's built-in help (**NOTE:** Most of these targets
  are purposefully made unavailable and won't do anything!)
- `setup-env`: Create a Python venv (in `doc/.venv/`) suitable for building the
  documentation.
  This tries not to do unnecessary work: If you already have a `doc/.venv/`, it
  will simply install the dependencies the build requires.
- `install-pdf`: Build and install PDF renderings to `doc/pdfs/`.
- `clean`: Clear out all packaged code and Sphinx-generated files.
- `distclean`: All of the above, plus the Python environment.

`make help` always shows the most up-to-date list of supported document targets.

#### `scripts/`

This directory contains utility scripts (and the documentation's
`requirements.txt`) used to implement the `make` targets above.

- `scripts/setup_env.sh` creates and validates a suitable Python environment,
  independent of the documentation build.
  It uses the sibling `requirements.txt` file, and can be run anywhere you want
  to create a `.venv/` suitable for building SAW documentation (though in most
  cases, you'll just be running `make setup-env` in `doc/`).

### Troubleshooting

1. If the build succeeds, but you aren't seeing all of the expected changes:

   Try running `make clean` before rebuilding; Sphinx may have failed to
   detect the changes you made, and you're seeing stale/cached output.
2. If you have unresolved reference warnings:

   Sphinx has an incredibly robust cross-reference system, but it is easy to get
   "wrong".
   If using Markdown/MyST, make sure you are using references according to [this
   documentation](https://myst-parser.readthedocs.io/en/latest/syntax/cross-referencing.html).
3. If the build fails:

   Try a full `make distclean` to wipe out the `.venv/` directory and start again in
   a fresh environment.

If you still have trouble, you've likely uncovered a bug in the system.
Please [open an issue](https://github.com/GaloisInc/saw-script/issues) detailing
the expected behavior, the observed behavior, and instructions to reproduce the
observed behavior.

## Understanding `doc/`

This directory is the intended source root for all SAW documentation.

### Contents

- The `Makefile` is explained in more detail [above](#makefile).

- `conf.py` is our Sphinx configuration, which has been heavily customized from
  the default Sphinx provides.

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

- The `scripts/` directory is where scripts relevant to building the
  documentation are located.
  This includes a `requirements.txt` pinning dependencies for the Sphinx build.

- `saw-lexer` is a small Python package implementing a SAWScript `pygments`
  lexer, so our documentation understands and properly renders fenced code
  blocks labeled ```````sawscript````.

- `sphinx-download-dir` is a Python package implementing an extension for Sphinx
  in the form of a _role_ (essentially, an inline element with some semantics)
  for creating full-directory downloads more easily.
  See [below](#code-examples) for usage detail.


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
- `saw-server/docs/`: An old Sphinx setup for SAW's Python remote API

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

We have implemented a small Sphinx extension, `sphinx-download-dir`, to make it
easier to provide full-directory downloads in your documents.

To use this feature:

1. Create your directory that should be downloadable somewhere in `doc/` (as
   long as it's somewhere in the tree, you'll be able to create a download
   link).
2. Take note of the directory's location, either relative to `doc/` or relative
   to the document where you would like to create a download link (either will
   work).
3. Add the link:

   ```markdown
   Check out my cool {download-dir}`download<path/to/dir>`!
   ```
   
   This will look for `path/to/dir` relative to this document; to look for it
   relative to `doc/`, prefix with a `/`
   (i.e. ``{download-dir}</path/to/dir>``).
   
That's it!

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
<scripts/requirements.txt>), you can manually activate the Python virtual
environment with `.venv/bin/activate`, and deactivate it again with
`deactivate`.

This ought not be necessary for most work on documentation.
