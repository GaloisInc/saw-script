from subprocess import check_output, CalledProcessError, DEVNULL

# -- Project information -----------------------------------------------------

project = "SAW Documentation"
copyright = "2025, Galois, Inc"
author = "The SAW Development Team"

# -- General configuration ---------------------------------------------------

extensions = [
    "sphinx_copybutton",
    "sphinx_download_dir",
    "hoverxref.extension",
    "notfound.extension",
    "myst_parser",
]

myst_enable_extensions = [
    "amsmath",
    "attrs_block",
    "colon_fence",
    "deflist",
    "dollarmath",
    "replacements",
    "smartquotes",
    "strikethrough",
]

# -- Options for markup ------------------------------------------------------

primary_domain = None

# -- Options for the nitpicky mode -------------------------------------------

nitpicky = True

# -- Options for source files ------------------------------------------------

exclude_patterns = [
    "_build",
    "Thumbs.db",
    ".DS_Store",
    ".venv",
    "developer",
    "**/code",
    "README.md",
]

# -- Options for templating --------------------------------------------------

templates_path = ["_templates"]

# -- Options for HTML output -------------------------------------------------

html_theme = "sphinx_rtd_theme"

git_describe = ["git", "describe", "--tags", "--exact-match"]
git_symref = ["git", "symbolic-ref", "--short", "HEAD"]

try:
    git_version = check_output(git_describe, stderr=DEVNULL, encoding="utf-8")
except CalledProcessError:
    pass
try:
    git_version = check_output(git_symref, stderr=DEVNULL, encoding="utf-8")
except CalledProcessError:
    git_version = "test-version"

# These context variables are used when instantiating
# doc/_templates/versions.html
html_context = {
    "VERSIONS": True,
    "current_version": git_version.strip(),
}

# Modifies the DOM corresponding to the versions pane to include everything in
# the JSON file written by CI when new versions are published.
html_js_files = ["versions.js"]
html_static_path = ["_static"]

# -- Options for LaTeX output ------------------------------------------------

pdfs: list[tuple[str, str, str]] = [
    ("llvm-java-verification-with-saw", "LLVM/Java Verification with SAW", "howto"),
    ("rust-verification-with-saw", "Rust Verification with SAW", "howto"),
    ("saw-user-manual", "SAW User Manual", "manual"),
]
"""Documents we wish to render to separate PDFs.

These documents are given as 3-tuples of strings:

(<document root directory name>, <document title>, 'howto'|'manual')

Usually, if you add something to the toctree in index.md, it will get an entry
here (or vice-versa).
The most notable exception is development/, where developer documentation (e.g.
the SAWCore external format reference) is stored.

The document root directory is assumed to contain a document named index,
defining the toctree for that document.
The contents of this index (other than the table of contents it defines) will
_not_ be included in the rendered PDF, so can be used for Web-specific
materials.

The title is what will render on the PDF's cover page.
This will usually match the title/first heading of the index document.

'howto' will use \\section as the highest level of organization, while 'manual'
will use \\chapter.
Generally speaking, the former is more appropriate for shorter/tutorial-style
documents, while the latter is best for longer/reference-style documents.
When adding new materials to the SAW documentation, it is worth testing both
styles to see what flows more naturally.
"""

latex_engine = "xelatex"
latex_documents = [
    (f"{doc_dir}/index", f"{doc_dir}.tex", title, author, style, True)
    for doc_dir, title, style in pdfs
]
latex_logo = "figures/galois.pdf"
latex_show_urls = "inline"
latex_elements = {
    "pointsize": "12pt",
    "fncychap": r"\usepackage[Sonny]{fncychap}",
}
