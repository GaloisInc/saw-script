#!/usr/bin/env python3

# Write available documentation versions to a JSON file understood by Sphinx and
# the ReadTheDocs theme/template.

import json
from pathlib import Path

cwd = Path.cwd()
versions = sorted(
    (
        item.name
        for item in cwd.iterdir()
        if item.is_dir() and not item.name.startswith(".")
    ),
    reverse=True,
)
target_dir = Path("gh-pages")
target_dir.mkdir(parents=True)
target_file = target_dir / "versions.json"
with target_file.open("w") as f:
    json.dump(versions, f)
