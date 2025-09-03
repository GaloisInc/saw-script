# Issue labels

The issue labels for saw-script are grouped by color into categories.
Administrative labels use warm colors and technical labels use cool
colors.

Issue labels should be used to reflect the _current_ state of the
issue.
For complex issues, the label set should be updated as understanding
changes and/or partial fixes are put in place.
The primary purpose of labels is to improve search and discovery as
issues are worked on; statistics and analysis (for which one would
want to leave certain labels in place even when they no longer apply)
is at most a secondary application.
In principle, when closing a complex issue whose labeling has changed
over time, it's nice to update the label set with all the labels that
_have been_ relevant; this improves discoverability for closed issues,
which is useful not just for analytics but also for investigating
regressions.
However, we shouldn't assume this will get done.

If reopening an issue because the changes that fixed it needed to be
reverted, or because it has regressed, check and update the label set.

The categories and their labels follow. 

## Primary issue properties (red)

* _breaking_ - marks changes that will break backwards compatibility.
Use this label to help ensure that concerns relative to such changes
(documentation, migration path, etc.) are attended to.

* _easy_ - marks issues that we expect to be easy to resolve. These
are likely to be good starting points for new contributors.

* _maybe fixed_ - marks issues where there's some reason to suppose
the issue might be resolved, but that requires further investigation
or confirmation. If the fix is confirmed, please remove the label
before closing the issue. For obvious reasons, generally should not be
applied to new issues.

* _missing cryptol features_ - marks issues related to features in
Cryptol that don't work in SAW.

* _needs administrative review_ - marks issues that need
administrative (rather than purely technical) review, e.g. to assess
relevance, priorities, or strategic planning.
Should be removed once this review has happened and administrative
questions have been answered.

* _needs design_ - marks issues that need (technical) design work to
resolve.
For example, something needs to be done but it isn't yet clear how to
accomplish it, or it has interactions with other things that need to
be clarified before work begins.
Also should be used when we haven't yet established requirements.
Should be removed once stakeholders have aligned on the needed plans.

* _needs test_ - issues for which we should add a regression test.
In principle this label can be removed once there's a pull request
that includes such a test (and re-added if that pull request is
abandoned, the test backed out, etc.) or failing that when such a
pull request is merged.
Also in principle this should never appear on closed issues; if a
test is needed it should be added before the issue is closed, or
failing that a new issue should be added covering just the test.
However, we shouldn't assume these updates will get done and in
particular searching for closed issues with this label is not expected
to be useful.

* _obsolete_ - marks issues that involve or depend on deprecated
code such that they are not worth pursuing.
For example, if there's a bug in a deprecated command such that it
sometimes crashes, in general the correct response for anyone seeing
the bug is to move away from the deprecated command and the bug itself
isn't worth fixing.
(This is not always the case; if it's not the case, don't use this
label.)
The issue should be left open until the deprecated code in question is
ultimately removed; this makes it easier to find if/when someone else
sees the problem.

* _priority_ - marks issues that are currently high priority for
whatever reason.

* _regression_ - marks issues that describe regressions, that is,
things that used to work but no longer do.
If a previous (now closed) issue regresses and a new issue comes in
documenting that, mark the new issue a regression and link it to the
previous manifestation.
If a previous (now closed) issue is found to have regressed without
a new issue having been filed, it may make sense to reopen it rather
than filing a new issue.
In that case, when reopening the previous issue, mark it as a
regression.

* _unsoundness_ - marks issues that can lead to unsoundness or
incorrect verifications.
Please be sure before applying this label, but please also don't
hesitate to use it when it's warranted.

* _usability_ - marks issues that get in the way of using SAW
effectively.

* _wontfix_ - marks issues that have not been fixed and aren't going
to be fixed.
This should only be applied to closed issues (that is, if applying it,
apply it when the issue is closed) and should only be used for issues
that are still relevant; that is, the issue is still valid but isn't
worth fixing for whatever reason.
Issues that aren't valid, turned out not to be bugs, stopped happening
on their own, were in code that was later deleted, etc. should not use
this label.
The purpose is to be able to retrieve these issues again from the
otherwise large and poorly-indexed body of closed issues.

## Secondary issue properties (black)

* _better-in-python_ - marks issues that can be resolved by switching
to the Python-based interface.

* _better-when-documented_ - marks issues whose root causes include
missing or wrong documentation.
Use this for any issue where that's true, regardless of whether it is
primarily a documentation issue or not.
Do not close the issue until the documentation issues have been
handled.

* _documentation debt_ - marks issues that involve previously
deferred, unhandled, postponed, or unfinished documentation tasks;
technical debt in documentation.

* _performance_ - marks issues that affect performance or include
performance problems.

* _tech debt_ - marks issues that involve previously incurred
technical debt.

The distinction between primary and secondary issue priorities is
specifically which ones we want to have stand out when looking at the
label set.

## Type of issue (orange)

* _type: bug_ - marks issues that report unexpected/unwanted behavior
or other problems.

* _type: enhancement_ - marks issues that describe improvements to
_existing_ capabilities.
Issues describing _new_ capabilities are feature requests.

* _type: feature request_ - marks issues that describe desired new
capabilities.
Issues describing improvements to _existing_ capabilities are
enhancements.

* _type: question_ - marks issues that are primarily asking questions.
The difference between a question and a more generic support request
is that a question is resolved once an answer's been found.
Questions will sometimes progress to more general support requests.
Sometimes they will also be of the form "is this behavior a bug?" in
which case the answer is often "yes" and the issue then becomes a bug
report.
Update the type label when these things happen.

* _type: support_ - marks issues that ask for help or support.
Not infrequently these will progress to be bug reports; at that point
change the type label.

These labels have a common text prefix so they sort together.
Issues should ordinarily have exactly one type label.

## Issue state (yellow)

We are currently not using issue state labels.

## Technical topics (pale green)

In general apply these if they appear relevant; the purpose of these
labels is to attract the attention of people who know about the topics
in question, and it's better to have the occasional false alarm than
to miss things.

* _topics: bitfields_ - marks issues that relate to SAW's support for
bitfields.

* _topics: error handling_ - marks issues that involve the way SAW
responds to an error condition.
It is common, but not universal, for issues that involve error
handling to also involve the messages printed as a result; use the
_topics: error messages_ label as well for these.

* _topics: error messages_ - marks issues that involve the messages SAW
produces when an error occurs.
(Use this label for warning and notice messages as well, if applicable.)

* _topics: memory model_ - marks issues related to the LLVM and/or
Crucible model of pointers and memory blocks.

* _topics: saw-core names_ - marks issues related to the URI-based
saw-core names.

These labels have a common text prefix so they sort together.
Use all that apply.

## Artefact type (dark turquoise)

* _documentation_ - marks issues involving documentation.
Don't forget to also select an issue type (typically _bug_, but
sometimes _enhancement_ or _feature request_).
The _better-when-documented_ label is for issues where someone
ran into problems because of bad or missing documentation;
the _documentation debt_ label is for issues where necessary
documentation changes got left off or forgotten in the past.
None of these are mutually exclusive.

* _test assets_ - marks issues involving test programs and/or other
test assets.
This includes, for example, bugs in test programs, and test programs that
don't behave deterministically.
Use _tooling: test infrastructure_ to label bugs in test infrastructure.
Use the _CI_ label for issues involving the CI infrastructure, including
running tests in the CI system.

## Project tooling (lime green)

* _tooling: build system_ - issues involving SAW's build system.

* _tooling: CI_ - issues involving the CI/CD scripts or processes.
For test or testing problems, use this label only if the CI mechanisms
are involved; otherwise use _tooling: test infrastructure_ for
infrastructure issues and _test assets_ problems with individual
tests.

* _tooling: test infrastructure_ - issues involving test
infrastructure, test execution, or making SAW more testable.
Use _test assets_ instead for problems with individual tests.

* _tooling: release engineering_ - issues involving releases, release
processes, making releases, or other release engineering concerns.
This includes processes related to snapshots and nightlies.

## Project subsystems (cornflower blue)

* _subsystem: crucible-jvm_ - issues related to Java verification
using the crucible-jvm tooling.

* _subsystem: crucible-llvm_ - issues related to LLVM bitcode
verification using the crucible-llvm tooling.

* _subsystem: crucible-mir_ - issues related to Rust verification
using the crucible-mir and mir-json tooling.

* _subsystem: crucible-mir-comp_ - issues related to Rust verification
and composition with crucible-mir-comp or crux-mir-comp.

* _subsystem: cryptol-saw-core_ - issues related to the
Cryptol-to-saw-core translation in the cryptol-saw-core package.

* _subsystem: hardware_ - issues related to verification of hardware.

* _subsystem: MRSolver_ - issues related to the Mr. Solver
monadic-recursive solver in Heapster.

* _subsystem: saw-core_ - issues related to the saw-core
representation or the saw-core subsystem.

* _subsystem: saw-core-coq_ - issues related to converting saw-core to
Gallina for use with the Coq/Rocq theorem prover.

* _subsystem: saw-python_ - issues related to the Python bindings for
the RPC SAW server.

* _subsystem: saw-remote-api_ - issues related to the SAW server and
its RPC bindings.

* _subsystem: x86_ - issues related to verifying x86 binaries via Macaw.

* _subproject_ - issues involving one of the various subprojects SAW
depends on.
Note that this intentionally does not have the "subsystem:" prefix as
the string "subsystem: subproject" is confusing.

# Pull request labels

On GitHub pull requests use the same label set as issues.
The labels defined in the previous section should be used only for
issues, not pull requests.
There is no need to mirror the labels on an issue into a pull request
meant to address it.
(However, if making a pull request without an issue, then please do
apply any relevant issue labels; this improves later discoverability.)

Also please remember to add any pull request properties that apply.

There is one category of pull request labels.

## Pull request properties

* _PR: dependency bump_ - use this to mark pull requests that adjust
dependency constraints.
(Other than via git submodules; use _PR: submodule bump_ for those.)

* _PR: keep updated_ - add this label to ask Mergify to merge the
trunk into your pull request branch for you when the trunk updates.
Because of the assorted risks associated with more than one party
applying changes to the same git branch, this should generally be used
only for branches that are not currently under active development.

* _PR: ready to merge_ - this label asks Mergify to merge your pull
request as soon as there's both an approval and a successful CI run.
We are no longer using this Mergify feature and expect to remove
support for it in the near future.

* _PR: submodule bump_ - use this to mark pull requests that change
git submodule references.
(Changes that involve other version bumps should use _PR: dependency
bump_.)

# Adding labels

In order to keep this documentation up to date, if proposing new
labels (or changes to the existing labels), please include a pull
request that updates this file.
