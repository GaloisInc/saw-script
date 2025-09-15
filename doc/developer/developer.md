# SAW development process, conventions, and standards

This document is intended as a reference for the procedures and
conventions we use when working on SAW.
Our goal is to have processes that are able to
- consistently yield reliable software artifacts;
- avoid mindless adherence to procedure or form over function;
- quickly incorporate improvements and get them into user hands; and
- allow new contributors to have an immediate impact.

Topics include:

- dependencies and setup;
- dependency management;
- building as a contributor / developer;
- testing;
- continuous integration;
- issue tracking;
- documentation;
- git usage; and
- producing and publishing release artifacts.

This file is a supplement for [CONTRIBUTING](../../CONTRIBUTING.md)
and does not repeat things documented there.

This is a living document that is not (and possibly cannot be)
comprehensive. If something is missing or unclear, or if you have
suggestions for improving our processes, please file an issue or open a
pull request.
This is especially important when you're new to the project as that
provides a perspective that's easily lost once you're embedded in
things.


# Dependencies and Setup

This material is largely covered in
[the README](../../README.md) and [CONTRIBUTING](../../CONTRIBUTING.md).

One remaining issue is: exactly which solvers are needed?
The set of solvers found in
[what4-solvers](https://github.com/GaloisInc/what4-solvers)
is sufficient (largely by definition: the point of what4-solvers is
to provide one-stop shopping for the needed solvers) but that only
pushes the question back one notch.

From time to time we have found that a proof in the test suite that
previously worked with one version of a given solver no longer works
(times out, OOMs, etc.) with a newer version.
In response to this we have, on an ad hoc basis, included extra
versions in what4-solvers and arranged to run them when needed.
It has become clear that some additional structure is needed, but it
isn't yet clear what.
This is currently being handled in issues
[#1772](https://github.com/GaloisInc/saw-script/issues/1772) and
[#390](https://github.com/GaloisInc/saw-script/issues/390).


# Dependency Management

## Mechanisms

With the tooling we're using (`cabal`) there are three ways to depend
on something, besides expecting it to be already installed on the
system: (a) as an external package to be brought in by cabal; (b) as a
git submodule to be checked out as part of the tree; or (c) as a git
repository reference to be cloned on the fly.

It is easier to make updates to things that are submodules: updating
an external package requires making a release to Hackage.
Also it's apparently difficult or maybe impossible to carry patches to
packages fetched from Hackage.
A submodule reference can if necessary be temporarily changed to point
at a fork repository.
It's also easier to look at the code of a submodule (which sits in the
tree) vs. the code from a package (which is hidden in a corner
somewhere).

Moving things to submodules temporarily is also undesirable; adding
and removing submodules is at a minimum disruptive and sometimes
breaks git.

Meanwhile, cloning on the fly is undesirable (the download and build
phases should be clearly separated, in case one is disconnected, and
also to enable auditing what's been downloaded), and possibly risky.

Policy therefore is to choose between (a) and (b) based on long-term
need and not to use (c), but if a temporary measure is needed (c) is
better than setting up a transient submodule.

Note that while many of the submodules have their own submodules, our
practice is to include everything required as first-level submodules
in the saw-script repository.
(This is workable because everything is Haskell managed with
```cabal```.)
Thus when you run ```git submodule --init``` it is _not_ necessary
to specify ```--recursive```, and in fact doing so will check out
additional unused subtrees and waste your disk space.

## Versioning

Versions need to be pinned down to avoid surprises.
This is why we keep cabal freeze files for each supported GHC version.
However, it also means new versions have to be pulled in explicitly, and
this takes work.
Unfortunately there doesn't seem to be any better way to handle it that
doesn't also take work.

In an ideal world someone would keep an eye on each upstream package
and, with knowledge of relevant considerations (e.g. what has to be
updated when it changes, the quality of its release processes, etc.)
maintain a recommended version.
Then one could subscribe a project to that feed of versions, and get
mostly non-breaking updates at useful intervals.
Unfortunately that feed doesn't seem to exist, so what tends to happen
instead is that things get left alone until something finally breaks,
and then a lot of updates need to be done at once because one has
fallen behind everywhere, and that tends to be disruptive.

If you are familiar with the state of affairs regarding any particular
upstream package we depend on, and when it is and isn't a good time to
update, please feel free to suggest or recommend against updates
accordingly.


# Building

This material is covered in
[the README](../../README.md) and [CONTRIBUTING](../../CONTRIBUTING.md).


(testing)=
# Testing

There are multiple test suites in the SAW repository.

The main test suite is called `integration-tests` and the contents
can be found in the `intTests` directory.

<!--
  -- Keep the list of tests in sync. There are four copies:
  --    o here
  --    o .github/workflows/ci.yml
  --    o build.sh
  --    o and of course the definitions in the *.cabal files
  -->

The following can be run with `cabal test`:

- `integration-tests` (this is the main test suite)
- `saw-core-tests`
- `cryptol-saw-core-tests`
- `saw-core-coq-tests`
- `crux-mir-comp-tests`

There are two other sets of tests:

- `saw-remote-api tests`
- `mr-solver-tests`

The saw-remote-api tests can be run with the script
`saw-remote-api/scripts/run_rpc_tests.sh`.
The other one is run by the CI but is not currently really intended
to be run by hand.

The s2n proofs that are also run by the CI are driven by scripts found
in the [s2nTests](s2nTests) directory.


# Continuous Integration

There are three notable topics not covered in
[CONTRIBUTING](../../CONTRIBUTING.md): testing release processes,
testing with unlocked dependencies, and monoculture.

Also note that we could in principle check some things in pre-commit
hooks rather than as CI tests, but there's little of use that can be
checked that way without taking irritatingly long, so we don't.

## Testing release processes

One of the things that's useful to do in a routine CI run is to
generate a dummy snapshot release (as in, the release artefacts, like
source and binary tarballs, documentation PDFs, etc.) to make sure this
generation isn't broken.
We don't currently do this, but we probably should.

## Testing with unlocked dependencies

Another useful thing to do is to see what happens if you build against
the latest version of all the things you depend on.
If that fails, it's probably something you want to know about, even if you
don't do anything about it right away.

There are at least four subcategories of this (submodules,
dependencies on packages we control, dependencies on packages we
don't, and external installed dependencies) that require different
handling.
Currently we don't do any of this, at least not as part of the CI runs.
It isn't clear that GitHub Actions is the right venue for it, either.

## Heterogeneity and monoculture

One of the risks with containers and slickly packaged CI testing and
whatnot is that your testing environment becomes a monoculture, and
that makes your system brittle.
Portability is less of a problem with Haskell code than in other
contexts, but all the same we try to avoid this by testing on multiple
OSes and multiple target CPUs.

Currently we build on two supported Ubuntu LTS releases on x86, two
MacOS releases (one x86 and one arm64), and Windows.
It's possible we should add something else, maybe using our own runner.


# Issues

See [issue-labels.md](issue-labels.md) for documentation of the issue
labels we use.

## When to file an issue

We do not require that every pull request correspond to an issue.
It is fine if there are several pull requests before an issue is
finally resolved (as long as what's happening is reasonably clear to
passersby) and also fine to make pull requests without an issue.

Create an issue if:

- there's a problem that you're not going to get to right away;

- there are complicated circumstances that should be written down,
or there's a problem that someone might want to be able to find
again easily later; or

- there needs to be a discussion about what to do, in order to
gather consensus or consult with stakeholders.

Don't create an issue if you already have a patch, unless one of these
circumstances applies or there's some other reason to specifically
create an issue; just file a pull request.
This is especially true for minor changes.
Changes that are _not_ likely to be searched for again later should
be kept out of the issue database to the extent reasonably possible.

Note that if you are searching closed issues to try to find something
you vaguely remember seeing go by, you may want to also search closed
pull requests.
Fortunately, on GitHub this is extremely easy. 


# Documentation

So far there is nothing that needs to be said here that isn't in
[../../CONTRIBUTING.md](CONTRIBUTING) or [../README.md](doc/README).


(git)=
# Git Usage

(rebasing)=
## Rebasing

Rebasing is an extremely contentious topic.

On the one hand, detractors correctly point out that rebasing throws
away history and context: if you write a change on top of commit A
and then later move it on top of commit B, you have lost that original
context and can't get it back.
If you later find that it worked when you wrote it but now it doesn't,
you've given up any hope of being able to figure out why by examining
the history, or of reproducing your original context.
This arguably defeats a lot of the purpose of keeping history in the
first place.

On the other hand, advocates correctly point out that a history that
doesn't fork is easier to examine, both manually and via operations
like `git blame` and `git bisect`.
They also could, but usually don't, correctly point out that git has
a number of design and user interface bugs that make merge commits
awkward or problematic to deal with.

The simplest solution to both of these sets of concerns is to not use
git, since other tools exist that both let you rebase while keeping
history and also handle merge commits better.
However, currently this is not feasible.

Here are some of our thoughts on the matter:

- A short-term topic branch is basically equivalent to a set of
  patches, and like a set of patches there's no real reason not to
  update any or all of them as needed while you're working.
  There is no real downside to retconning bugs you find while working,
  or updating the trunk underneath what you're doing, provided that
  you take reasonable caution (e.g. make sure _all_ your changes still
  work, not just the most recent) and rebase is how you do those
  things.

- In particular, using `git rebase -i` to rearrange your commits
  without moving them to a new context does not share most of these
  risks.

- As your topic branch or patch set becomes larger, more complicated,
  and/or more subtle, however, the risks of this kind of adjustment
  increase sharply.
  (This is also true if something large, complicated, and/or subtle
  lands on the trunk.)
  One technique for helping cope with this is to keep the original
  pre-rebase changesets on an additional archival branch.
  Unfortunately git provides no infrastructure support for this so it
  doesn't scale well; however, with luck you don't produce all that
  many large, complex, and/or subtle topic branches.

- By the time you get to long-running major feature branches, rebasing
  is generally inadvisable.
  Merge instead.

- When working on a long-running major feature branch, which in the
  context of SAW likely includes a lot of research work, merge the
  trunk into your branch early and often.
  The more often you merge, the simpler each merge is and the less
  likely it is that something will go off the rails.
  Also, even though this sort of tightly braided history is against
  the git conventional wisdom, it nonetheless gives the most leverage
  in future investigations.

- Before merging a major feature branch, or even a topic branch that's
  been around for a while, merge the trunk into it.
  This helps avoid surprises after merging your branch into the trunk.
  GitHub will let you merge any branch that doesn't generate merge
  conflicts.
  We make a point of having the CI test the candidate merge and not
  just the head of the pull request, but that doesn't always prevent
  unpleasant surprises.
  (And sometimes it means you get CI failures you can't reproduce
  locally, which can then be quite confusing.)

The assorted git UI bugs related to merge commits can mostly be worked
around via add-on tools.
The deeper problem that it's good to be cautious about is that git
believes that merge commits are semantically null and uninteresting.
(This manifests in a variety of situations where merge commits are
treated as second-class or even ignored.)
This is fine for small commits with widely separated changes, but gets
less and less true the more manual attention a merge takes.
If merging branch A with branch B requires updating A's code to take
account of B and updating B's code to take account of A, especially
in cases where some of these updates need to be applied in places that
the purely textual merge doesn't touch, you are well into the danger
zone.
In these cases it can be a good idea to take precautions, like
applying some of the changes from one branch to the other explicitly,
and sorting out the results, before doing the official merge.


(releases)=
# Releases

Long-term stable branches associated with releases are periodically
forked off from the trunk; these diverge from the trunk until they
reach end-of-life.
(They are not merged back into the trunk or into each other.)
These branches are named e.g. `release-1.1`.

Each release is tagged on its stable branch.
If an update to a released version is needed (e.g. security fixes,
critical bug fixes, or potentially a collection of feature updates
leading to a point release) these are applied to the stable branch
with additional topic branches and pull requests.

In general changes made to release branches should be made to the
trunk first, validated there, and then cherry-picked into a separate
topic branch for merging into the release branch.
Exceptions may exist when necessary.

Currently our process is to freeze the trunk in preparation for a
release, so the changes on the stable branch leading to the release
are generally limited to immediate release prep tasks.
However, this is not a given and it is reasonable to polish a release
branch for some period of time before making the actual release.

The full release procedure appears in [releasing.md](releasing.md).
