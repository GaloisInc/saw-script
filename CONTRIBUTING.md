# Contributing to SAW

This document covers what you need to get started contributing to SAW.
Further and more detailed information can be found in
[doc/developer/developer.md](doc/developer/developer.md).

Topics include:

- dependencies and setup;
- building as a contributor / developer;
- testing;
- continuous integration;
- issue tracking;
- documentation;
- Git operations (organizing, branching, and merging this repository); and
- coding style

This is a living document that is not (and possibly cannot be)
comprehensive. If something is missing or unclear, or if you have
suggestions for improving our processes, please file an issue or open a
pull request.
This is especially important when you're new to the project as that
provides a perspective that's easily lost once you're embedded in
things.


# Dependencies and Setup

There are a few additional bits and pieces you will want to have
available when working on SAW.

A number of bits in corners use makefiles to rebuild or clean things.
You will want to have GNU make (`make` or `gmake`) available.

You will also want to put the `bin` dir that the SAW build generates
on your `$PATH`, perhaps in general but at least while you're actively
working on SAW.
There is, for the time being at least, a reason for this beyond
convenience: when you run the `intTests` test suite, it runs `saw`
from the path.
If there's no `saw` on your path, it fails confusingly.
If there's some _other_ `saw` on your path, it'll run that one instead
of the one you just built.
This is issue
[#1753](https://github.com/GaloisInc/saw-script/issues/1753);
with luck it will get fixed soon.

Currently the manual (and other buildable documentation) is built with
Sphinx.
All you need for this is a reasonably current Python 3 install.
The rest is downloaded into a virtual environment on demand.
If you want to set this environment up in advance, e.g. because you
expect to be working offline, you can run ```make setup-env``` in
the ```doc``` subdirectory.
See the [doc/README.md](documentation README) for further information.
Also see issue
[#2197](https://github.com/GaloisInc/saw-script/issues/2197)
which is tracking the state of documentation build and deployment
improvements.

If working on LLVM verification you will probably need LLVM and Clang
available, e.g. to create or update LLVM bytecode files used in the
test suite.
Except in special cases the exact version is not normally particularly
important and any copy of Clang that came with your OS is probably
sufficient.

If working on MIR/Rust verification you similarly will need `mir-json`
(as noted in README.md) and also a copy of the version of the Rust
compiler that `mir-json` supports.
See the
[mir-json installation instructions](https://github.com/GaloisInc/mir-json#installation-instructions).

To work with saw-core-coq you'll need Coq (and OCaml); the recommended
way to get them is via opam.
We are currently using OCaml 4.x and not OCaml 5.x.
Transition to OCaml 5 should be guided by upstream support in Coq.

Finally, to run the full set of integration tests you will need a full
set of solvers, which at some times and in some cases includes
multiple versions of some solvers.
The easiest way to get this is to download a
[what4-solvers binary snapshot](https://github.com/GaloisInc/what4-solvers).

If you use haskell-language-server, SAW ships with a `hie.yaml` that
should be sufficient to get it to understand the project structure.
There are also some tools for vim and emacs available in the tree.


# Building

See guidance in [README.md](README.md) (under "Manual Installation")
for information on building SAW.

Normally you should build with `build.sh`; however, under some
circumstances it may sense to run `cabal build` by hand to recompile
only part of the system.

With a fresh tree, if you have never run `build.sh`, you must first
run `build.sh gitrev` to capture the git checkout state.
(And you should rerun this when you change your git checkout.)
You should also do this before attempting to build the Docker
containers.

Once the git data has been updated you can run `cabal build` or other
cabal commands as needed.
However, running `cabal` by hand is not the recommended or supported
build interface and additional manual steps may appear in the future.
For example, be aware that while `build.sh` compiles the test code as
part of the default build, `cabal build` does not.

You can also set the environment variable `SAW_SUPPRESS_GITREV` to
something nonempty to prevent updating the git checkout state.

This is not recommended except when actively developing; however, when
actively developing it avoids recompiling certain slow things (that do
not actually need to be rebuilt) over and over again every time the
git state changes.
If you use this method be sure to include the correct git hash when
reporting issues, particularly when pasting panic messages.
This is a hack and will hopefully be replaced by some other better
solution when we can find one.

As a contributor there are a few additional quirks to be aware of.

A second is that `build.sh` runs `git submodule update --init` and
this will silently reset any uncommitted submodule changes you are
trying to test.
When tinkering with submodules it is best to build explicitly with
`cabal build`.
See `build.sh` itself for what to ask `cabal` to build.
When doing this also beware that the step that copies the compiled
programs into `bin/` is a function of `build.sh` and not `cabal`
and also should be done by hand if needed.

These issues may be resolved in the future; see
issue [#2063](https://github.com/GaloisInc/saw-script/issues/2063).

## Dependency freezing

To ensure repeatable test results, our CI system uses
`cabal.project.freeze` files to fix the version of all dependencies
prior to building. It uses one of several version freezing files, each
named `cabal.GHC-<VER>.config`, for GHC version `<VER>`.

We recommend building and testing using these files unless your explicit
goal is to assess compatibility with different library versions. To do
so, run the following before building or testing:

    ln -s cabal.GHC-<VER>.config cabal.project.freeze

## Build system updates

After any update to the Cabal project structure (new subpackages, new
libraries, moving package elements around, etc.) regenerate the
`hie.yaml` file used by haskell-language-server.
The procedure for this is:

- Commit your changes first (so the commit hash recorded in the new
  hie.yaml reflects your changes)
- Run mkhie.sh: `./mkhie.sh > hie.yaml.new; mv hie.yaml.new hie.yaml`
  (doing it in two steps prevents git from spuriously reporting that the
  tree is dirty)
- Examine the diff to hie.yaml in case something broke
- Commit hie.yaml with a commit message like "Regen hie.yaml"


# Testing

The primary test suite for SAW is called `integration-tests` and can
be run with `cabal test integration-tests`.

Ideally one runs at least `integration-tests` locally before
committing, but it takes long enough (this will only get worse as
coverage improves and the test suite grows) that people will run only
a few tests pertinent to their changes and let the CI run the rest in
the background.

The integration tests live in the `intTests` directory.
For more information about running individual tests and adding new ones,
see the `intTests` [README file](intTests/README.md).

There are several other sets of tests in the saw-script repository;
see [doc/developer/developer.md](doc/developer/developer.md#testing) for
a rundown.


# Continuous Integration

SAW uses a CI system based on GitHub Actions to run tests.
This runs not just the integration test suite described above, but
several other test suites as well.
It also runs several large proof developments, many for the [s2n TLS
library](https://github.com/aws/s2n-tls), to make sure that these
continue to succeed.

The CI runs tests on (the head of) every pull request, and also
periodically on (the head of) the trunk.
It does not test intermediate commits; if you want every commit
tested, you need to push them one at a time.
Sometimes this is useful; other times it's a waste of test resources.
Use your judgment.

Be aware: for pull requests, the CI tests the commit that would result
from merging with the trunk.
If the pull request's branch is behind, this may be materially
different from the tip of the pull request branch.
This can sometimes result in unexpected test failures.

Currently the tests run on pull requests and the periodic tests run on
the trunk are the same, but it is likely that in the future there will
be additional tests in the periodic runs.
(The main stopper for this is sorting out how to get adequate
notification for failures.)
There is a local convention that the environment variable `$CI_TEST_LEVEL`
controls how much gets run.
SAW doesn't currently use this but any upcoming scheme with additional
tests probably will.


# Repository Organization

The top-level repository directories are:

* `doc` - Documentation, including tutorials and the SAWScript manual.

* `examples` - Various examples of using SAWScript.

* `exercises` - Further examples, organized as exercises for the student.

* `deps` - A location for other dependencies included as Git submodules.

* `cve-reports` - Infrastructure for security audits of dependencies.

* `vim-saw` - Support bits for using vim.

* `saw-version` - A library encapsulating the build version data.

* `saw-core` - Source code for the SAWCore intermediate language used
  within SAW.

* `cryptol-saw-core` - A library for translating
  [Cryptol](https://cryptol.net) code into SAWCore.

* `saw-core-aig` - A library for translating SAWCore to And-Inverter
  Graphs.

* `saw-core-coq` - A library for translating SAWCore to Coq's Gallina
  language.

* `saw-core-sbv` - A library for translating SAWCore predicates to SMT
  queries using the [SBV](http://leventerkok.github.io/sbv/) library.

* `saw-core-what4` - A library for translating SAWCore predicates to
  solver queries using the [What4](https://github.com/GaloisInc/what4)
  library.

* `saw-central` - A library containing the bulk of SAW.

* `saw-script` - A library containing the SAWScript interpreter.

* `saw-server` - Library source for a server that provides a remote API to
  SAW based on JSON-RPC.

* `saw` - Source for the `saw` executable.

* `saw-remote-api` - Executable entry point to serve the remote API.

* `saw-tools` - Additional executables.

* `saw-python` - a Python client for the remote API.

* `crucible-mir-comp` - Support library for crux-mir-comp.

* `crux-mir-comp` - A version of [Crux](https://crux.galois.com/) that
  can perform modular analysis of Rust code using a form of contracts.

* `verif-viewer` - A tool for visualizing verification summaries.

* `intTests` - The central test suite for SAWScript.

* `s2nTests` - Additional tests for SAWScript, confirming that
  verifications involving the s2n library continue to work.

* `otherTests` - Some further tests for individual components.

* `dist-newstyle` - Transient build directory used by `cabal`.


# Issue tracking

We use the
[GitHub issue tracker in the saw-script repository](https://github.com/GaloisInc/saw-script/issues)
to manage bug reports and other tickets.
When filing an issue please search quickly to see if the same issue
has already been reported.
(There is no need to search exhaustively or spend a lot of time
checking old issues, but please do make a quick check.)
If feasible please label your issues when filing.
This helps make sure the right people see them quickly.
(Also, don't worry about mislabeling -- labels are easily updated.)

The issue labels for saw-script are grouped by color into categories.
Administrative labels use warm colors and technical labels use cool
colors.
Every issue should have exactly one label from the yellow `type:`
labels.
Note that GitHub has recently added a separate "Type" field to issues;
we do not use this, partly because of the cost of converting the
existing issue database and partly because odd technical choices in
the implementation so far make it unsuitable.

The available issue labels are documented in
[doc/developer/issue-labels.md](doc/developer/issue-labels.md).


# Documentation

SAW's major user-facing documentation consists of the
[doc/manual/manual.pdf](SAW manual)
plus two (soon to be three) tutorials:
[doc/tutorial/tutorial.md](LLVM and Java verification) and
[doc/rust-tutorial/tutorial.md](Rust verification).
Other user-facing documentation includes the top-level
[README.md](README) and [CHANGES.md](change log), as well as some (but
not all) of the assorted other READMEs and change logs scattered about
the saw-script tree.
The most notable of these are the
[saw-python/README.md](README) and
[saw-python/CHANGES.md](change log)
for the Python bindings.
Systematizing these so that the intended user-facing documents are
easily found is on the near-term agenda.

Other developer-facing documentation includes assorted other READMEs and
change logs, the [saw-server/docs](remote API documentation),
this file, its supplements [doc/developer/developer.md](developer.md)
and assorted other notes found in [doc/internal](doc/internal).
The eventual goal is also to be able to generate an internals manual
by running Haddock on the repository, but this is not yet in a
serviceable state.

The [doc/README.md](documentation README) is the first place to look
for info on building and updating the docs.


## Documentation Updates

Changes are not complete without relevant documentation updates.
This includes specifically:

- change log entries for changes with user-facing consequences;

- updates to [README.md](README.md), this file, and/or
[doc/developer/developer.md](developer.md) for developer-facing,
policy, organizational, or operational changes;

- updates to the manual;

- updates to the tutorial and examples if things in them become
obsolete;

- updates to summary sections of the internals manual;

- updates to the remote API interface docs;

- updates to doc strings/Haddocks/etc. for code objects in source
files, including such documentation for new code objects;

- bumping the documentation datestamp in
  [doc/scripts/epoch.mk](doc/scripts/epoch.mk)
  for any nontrivial updates to the manual or tutorial
  (see below).

In general changes will not be merged without their corresponding
documentation changes.

Note that as of this writing the state of the documentation is such
that a good chunk of the above is aspirational until things improve;
in particular we cannot expect updates to sections of the manual that
don't yet exist.
Similarly the current standard for the Haddocks is: don't make it
worse.
Comments that can be turned into Haddocks later are good enough for
now.

## Documentation Assistance

If you aren't a writer, or aren't a native English speaker, don't
despair!
We have people who are both, and they will be more than happy to help.
As the person making the technical changes, you are by far the best
positioned to explain what's going on.
The more of that you can get written down, the better, even if it's
hard to read or the English is half Mandarin grammar or whatever.
It is much easier for someone who is a writer (but doesn't really
understand what you're doing) to tidy up such text than to write the
whole thing from scratch.
If you would like help with writing, say so when you file a pull
request, or ask out-of-band.

## Documentation Tools

The miscellaneous documentation files scattered around the tree
(e.g. all the various READMEs) are written in Markdown.
Markdown is more of a concept than a standard; the condition of
satisfaction for changes is that these files render acceptably
in GitHub's Markdown viewer.
Note that when reviewing a pull request you can open a file in that
viewer via the "..." menu in the top right corner of each file's
diffs; choose "View File" there.
The [GitHub Flavored Markdown spec](https://github.github.com/gfm/)
as well as the
[Writing on GitHub](https://docs.github.com/en/get-started/writing-on-github)
page can be useful references.

The larger documents are currently written either in Markdown or
ReStructured Text and built with Sphinx.
Updates should render correctly in the built version.
The Sphinx build uses
[MyST](https://myst-parser.readthedocs.io/en/latest/intro.html),
which also supports roles, directives, and other concepts from
ReStructured Text.
Ideally updates should also render correctly in GitHub's viewer, but
this may not always be feasible.

The [CommonMark specification](https://commonmark.org/) is an attempt
at standardizing a 'core' Markdown that is "strongly defined" and
"highly compatible".

The various documentation builds are orchestrated with (GNU) make.

All of these source formats are themselves plain text.
This allows managing the documentation source files with git.

## Writing Documentation

There are several practices that we attempt to follow with
documentation sources.
These are intended to help restrict diffs to the text actually
changed, which make diffs smaller and easier to read, which in turn
makes changes easier to review (and easier to merge) and considerably
reduces development friction.

1. Don't generate long lines.
   The edit width (that is, the window size) for documentation is 80
   columns.
   Have your text editor word-wrap at somewhere between 60 and 70
   columns so there's a right margin, like in this file.
   (Emacs defaults to 70 and that's fine.)
   Also, don't insert extra spaces to make paragraphs align flush
   right.
   With a fixed-width font this is significantly harder to read, and
   it's also a headache to edit.

2. New sentence, new line.
   When starting a new sentence, begin it on a new line.
   Don't reflow whole paragraphs; reflow only single sentences.

3. Avoid making changes to lines you aren't actually making substantive
   edits to.
   Sometimes this means introducing an extra line break or two where
   you otherwise might reflow.

4. Commit whitespace and formatting (source formatting/layout) changes
   separately from content changes.
   (Thus, if you end up with too many extra line breaks or the like,
   such that things get ugly or unreadable, fix it up as a separate
   commit.)
   Document such changes in their commit messages to help reviewers
   skip over them.

5. Embedded links can be long and not play nicely with word-wrap; if
   one gets ugly, put it on its own line.
   If it nonetheless falls off the right edge of the screen, we need
   to just live with that.

6. Bump the documentation date, if there is one, when you make
   anything more than trivial content changes.
   The date for the manual and tutorials lives in
   [doc/scripts/epoch.mk](doc/scripts/epoch.mk).
   This is the date that appears, for example, on the front page of
   the manual, so it should reflect the date of last revision.

If you find that your editor is violating these principles for you
(e.g. refusing to let you have reasonable-length lines, or reflowing
text without being asked) and you can't figure out how to stop it, ask
for help.

A couple additional tips for writing effective Markdown:

- You need a blank line before the first entry of a list.
  If you leave the initial blank line off, strange things happen.

- Blank lines between list entries affect the resultant formatting;
  give each list blank lines or not consistently.

- The whole of each list item should be indented past the bullet point.
  This normally doesn't matter if you have a single paragraph, but if
  you want multiple paragraphs or have other markup it can be important.

## Updating Prebuilt Copies

For some of the large documents (currently without much intentionality
or pattern) a prebuilt PDF file is included in the repository.
This is for the use of people browsing in their local checked-out
clones of the tree, or on GitHub, who may not want to (or be able to,
respectively) build the documentation themselves.
These copies should be updated whenever any of their sources change,
using the following procedure:

1. Commit all the sources.

2. When necessary (for changes that affect text that propagates via
the SAW executable, such as the doc strings for the SAW intrinsics),
rebuild SAW itself.

3. Rebuild the PDF.

4. Commit the updated PDF with a commit message along the lines of
   "Regenerate the prebuilt manual".

This makes sure that all the ingredients are fully up to date and that
any and all metadata built into the PDF reflects the commit that
changed the text.


# Git Procedures

The following are the basic points needed to work successfully in this
repository.
For further discussion, rationale, etc. see 
[doc/developer/developer.md](doc/developer/developer.md#git).

## Branching

It is possible to spend vast amounts of time arguing about Git
workflows, and quite easy to concoct elaborate schemes where one
spends more time feeding Git than getting real work done.
We aim to avoid that.

The branching procedure in this repository is as follows:

- There is a single trunk branch, called `master`.
This is the current development version of SAW, and where nightly
builds are taken from.

- Development work is done on short-term topic branches, which are
then merged into the trunk by filing pull requests.
Pick a short and cogent name for each topic branch.
If you are working on an issue, start the branch name with the
issue number (e.g. 1234-fix-record-types).
Otherwise, it can be helpful to stick your username in to avoid
confusion but this isn't required.

- Releases are done on long-term stable branches.
See [doc/developer/developer.md](doc/developer/developer.md#releases).

- Pull requests should be merged by "merge", not "rebase" or
  "merge-squash".
  If you want to rebase or squash your changes, do it yourself before
  merging.
  When and whether to rebase remains a contentious (sometimes extremely
  contentious) topic.
  For discussion, see 
  [doc/developer/developer.md](doc/developer/developer.md#rebasing).

  Because of concerns about rebase and history loss, we specifically
  do not require history to be linear.
  If you run into problems caused by git's shortcomings handling
  merge commits (for example, how `git log` fails to report parents
  accurately) there are tools that can help, such as `tig` and `gitk`.

## Committing

Commits should be reasonably small, self-contained, do one thing at a
time, have a cogent commit message, and so forth.
Much has been written about this elsewhere and duplicating all that
here would not be particularly helpful.

Two further, sometimes overlooked, things to consider when deciding
what and how much to include in a single commit:

1. If we wanted to backport something in your work to a release branch,
would we be able to take the whole commit (allowing `git cherry-pick`)
or is only part of it relevant (which then requires much more work)?

2. If someone discovers six months from now that there's a subtle
problem of some kind and bisecting the problem reveals that this
commit caused it, is the commit small enough that you'll be able
to see why?

Also, please put whitespace changes, formatting changes, moving large
blocks of code, and the like in separate commits.
Mention in the commit message when the commit isn't supposed to alter
the behavior ("no functional change intended").

Because of technical shortcomings in the way git handles file renames,
as well as the difficulty of generating diffs across renames, please
put any renames in one commit and any changes to the files being
renamed into another.
(Other changes needed to accomodate the renames should go in the
second commit as well.)
For large renames you may need to commit the renames in batches to
avoid having problems merging across them.

Please also put commits that bump git submodules in their own commits.

Note that while it's possible to tidy up your commits with `git rebase
-i`, it's generally better to make them carefully in the first place
so you don't need to.
(However, it's still better to tidy them up afterwards than to not
tidy them, so don't hesitate to clean up as needed.)

If your topic branch falls significantly behind the head of `master`,
merge with it, or rebase, depending on the tradeoffs.
(As noted above, rebasing can be extremely contentious.
See [doc/developer/developer.md](doc/developer/developer.md#rebasing)
for discussion.)

It is better to not let this happen; that is, favor small branches
reflect a couple days' work rather than going off and coding for a
month and then trying to catch up.
If in doubt, merge early and often.
This applies both to merging `master` into your work and merging your
work into `master`.

When there's a rename change to merge with, it's almost always a good
idea to first merge with everything up to but not including the rename,
merge again specifically with the rename commit, then continue with a
third merge.
If the renames were committed in batches it is usually because you'll
need to merge with each one separately to avoid getting in trouble.
(This all applies regardles of whether you're actually doing `git
merge` or `git rebase`.)

Also please make sure all your commits, or at least all that exist by
the time you're ready to merge your changes, actually compile.
Ideally they should all pass the test suite as well, but this is
probably not realistic to check in detail.
(This does not apply to the intermediate states of changes that
have to be applied as multiple commits, like renames.)

## Reviewing

It is up to you whether to file a pull request when you start work on
a branch, when you feel the branch is ready to merge, or somewhere in
between.
Once a pull request is open, the CI will run every time you push more
commits; sometimes that's good, sometimes that's a waste of resources.
Use your judgment.
Mark pull requests that really aren't ready for review yet as drafts
to avoid confusion.
Note that some people may come and kibitz even in draft pull requests.
They're trying to be helpful; if it annoys you and you really want
your drafts to be ignored (most people actually don't), talk to them
and they'll stop.

When the pull request is ready, request a review from at least one
person, and preferably from every plausible reviewer at once.
Think of this as a quick ping to indicate that your pull request
is there, not as asking someone to do work -- if they don't have
time, they won't respond.
Also think of it as asking for one review from whoever gets there
first, not asking specifically for a review from each person.
If you have a change that some specific person ought to look at, add a
post to that effect and @ the person.
If you don't know who to request review from, go with the repository
maintainer (currently `sauclovian-g` for saw-script) or ask
out-of-band.

If you don't request a review, chances are either nobody will see
the pull request at all or they'll assume it isn't ready yet,
whether or not it's officially marked as a draft.

Some things to check for when reviewing a pull request:

- If the changes have user-facing consequences, is there a
  [CHANGES](CHANGES.md) entry?

- Has the documentation (not just the manual, but also the developer
  docs, tutorials, examples, etc.) been updated?

When reviewing, avoid the "request changes" option unless it is really
necessary that the concerns raised be resolved _and cross-checked_
before merging.
It turns out that when you do this, _you_ must re-review and approve
before the pull request can be merged, regardless of what anyone else
thinks.
This is usually neither necessary nor desirable.

For review comments, the person who posted the comment should be the
person to mark it resolved.
(If one even bothers; for small pull requests one might not.)
This rarely matters, but every so often someone accidentally misreads
or misunderstands a comment and pushes the wrong fix, and this makes
those situations less awkward.

When replying to a batch of review comments, if possible use the
"Files changed" tab rather than the "Conversation" tab.
On that pane you can "start a review" (even though you're really
replying) and then post a bunch of replies that will be collected up
as a single GitHub notification.
If you respond individually on the "Conversation" tab to a dozen
comments, you'll also generate a dozen emails; this is not critical
but it's nice to avoid.

In large pull requests it is nice to include the pertinent changeset
reference with each comment reply (as in "Fixed in a1b2c3d4").
Beware though that you must _push_ the changeset _before_ filing the
comment or GH won't index it properly.


## Merging

Pull requests must be reviewed before being merged, and must pass
the CI tests.
Specifically:

- At least one approving review is required.

- All the CI checks on the most recent commit must come up green.

(We do not have GitHub enforce these requirements, because we are all
notionally adults here and occasionally unusual circumstances arise.
Sometimes, for example, some of the CI checks may fail because of a
known problem on the trunk.
Such situations should of course be avoided but also should not be
allowed to hold everything up.)

Merge your own pull requests; you're the person who knows better than
anyone else when they're fully ready.
For the same reason, don't merge other people's.
If special circumstances apply (e.g. people going on vacation),
coordinate explicitly.
In particular, if you don't have access to merge your pull request,
say so.


# Coding Style

There are two incompatible schools of thought about coding style; one
is that style rules are mandatory, inflexible demands that must be
observed uniformly across thte code base at all times; the other is
that style guidelines are recommendations for writing legible code.
SAW follows the "recommendations" school of thought.

Most of the code in SAW is Haskell and most of it uses 2-space or
4-space indent because properties of Haskell's semantic whitespace
make that more or less inevitable.

The recommended edit width (that is, window size) for source files is
80 characters.
This is currently somewhat aspirational (many are wider, some much
wider) but the situation will hopefully improve over time.

Block comments should be formatted to a right margin of 60-70
characters (like documentation text), and not extend to the edge of
the window, to improve legibility.

To be precise: large blocks of text should not be more than 60-70
columns wide, because more than this interferes with the eyeball's
ability to do carriage-returns.
A large comment that's substantially indented can reasonably extend
further to the right, as long as it isn't off the edge of the window.
But it's rarely worth arguing with your editor to make this happen.

Conversely, code doesn't normally have the same horizontal density as
text so there's generally no need to cut it off before the edge of the
window.

When editing, please maintain the existing style of files.
Don't gratuitously reformat files.
If a file is significantly illegible, or too wide, and you're about to
make significant changes to it anyway, it's reasonable to reformat it
first, but please do that as a separate commit that includes no
functional changes.

See [doc/developer/conventions.md](doc/developer/conventions.md) for
some further and more specific formatting suggestions/requests.


# Copyright and License

Copyright 2011-2025 [Galois, Inc.](https://galois.com)

Licensed under the BSD 3-Clause License; you may not use this work
except in compliance with the License. A copy of the License is included
in the [LICENSE](LICENSE) file.
