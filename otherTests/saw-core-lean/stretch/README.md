# Stretch Probes

This directory contains manually-run stress probes that are useful for future
scalability work but are not part of the default Rocq-parity regression sweep.

The default `otherTests/saw-core-lean/test.sh` run deliberately excludes these
cases. A stretch probe may be large, slow, ahead of the current proof ergonomics
baseline, or carry historical `.good` files that document an old boundary rather
than the current expected result. Moving a probe back into `drivers/` or
`saw-boundary/` means it has become part of the required regression contract
again and its goldens must be made current.
