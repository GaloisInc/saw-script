# Formal Deprecation Process

SAW primitives, and thus their associated SAWScript built-ins, sometimes
become obsolete or are found inadequate and replaced.
The process by which that happens has three steps, as follows:

1. The decision is made to deprecate and eventually remove the objects
in question.
This can happen at the level of individual built-in elements (for example,
when replacing a function with an awkward interface or unfortunate name) or
at the level of internal units of functionality with possibly multiple
built-ins affected.
At this step the built-ins in question are marked for a deprecation warning.
They remain available by default, but referring to them will trigger a
warning.

2. The objects in question are made invisible by default.
Now, referring to the affected built-ins will fail unless the
`enable_deprecated` command is used.
In that case referring to them will still produce a warning.

3. The objects in question are removed entirely and are no longer
available.

In general any object or group of objects will move only one step per
release; that is, something first marked deprecated (so it warns) in
saw-script 1.2 will not disappear by default before saw-script 1.3 and
not be removed entirely before saw-script 1.4.
The time frame may be longer depending on the needs of downstream
users, the complexity of migration, and the cost/impact of keeping the
deprecated code in the system.

We may move faster if circumstances dictate, but hope not to need to.

Objects that have never appeared in a release, or that have never
moved past experimental may be removed without first being deprecated.
However, we aim to avoid this in cases where the objects in question
have gotten substantial use despite their formal status.
