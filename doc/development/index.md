# SAW Developer Documentation

These resources are mainly intended for developers working on the internals of
[SAWScript](https://github.com/GaloisInc/saw-script).

Currently, we document:

- The [SAWCore external format, `extcore`](sawcore-external-format/index), which
  is a text-based serialization of the low-level representation of SAWScript
  `Term`s.

  :::{warning}
  This document has not been updated for many years, and may be incomplete or
  inaccurate to the version of SAW for which this documentation was built.
  :::
- The fact that SAW has some [limitations](limitations).

  :::{warning}
  This document has not been updated for many years, and may be incomplete or
  inaccurate to the version of SAW for which this documentation was built.
  :::
- The `saw-script` [release process](releasing), such that any developer with
  merge-to-default access can easily create and reproduce SAW releases.
- [Changes](changes) to `saw-script`.

:::{toctree}
:hidden:

sawcore-external-format/index
limitations
releasing
changes
:::
