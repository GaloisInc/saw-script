# SAW code conventions

Please read the Coding Style section of [../../CONTRIBUTING.md](CONTRIBUTING.md)
before kibitzing.

The (few) points specifically noted here are ones we generally have
broad alignment on.

## Imports of data type modules

It's common to have library modules (whether or not in the stdlib)
that provide a type, often a container type, and are named after that
type.
These are typically intended to be imported qualified, because
otherwise they generally conflict with `Prelude`.

Examples in the stdlib include `Data.Map` and `Data.Set`.

Modules of this flavor should, preferably, be imported like this:

```
import qualified Data.Map as Map
import Data.Map (Map)
```

That is, import the module under its name (in this case `Map`) rather than
something else (`M`, `Mp`, etc.) and also import the type name directly.
For `Data.Map` this makes the type available as `Map` and all the
operations available as e.g. `Map.keys`.
This pattern seems to produce the best available tradeoff of verbosity
vs. legibility.

If you only need one of these imports and not the other, it's reasonable to
comment it out with `--` rather than delete it, as the need for one vs. the
other has a tendency to shift frequently even with minor code changes and
retyping the imports over and over again gets very tedious.
