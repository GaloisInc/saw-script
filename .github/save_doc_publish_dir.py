#!/usr/bin/env python3

import os
import re

# This script uses the current GitHub environment to determine the name of the
# directory to which documentation artifacts will be published for this job.

# Only the `master` branch and tags of the form `vM.m` (or `vM.m.p`) compute a
# meaningful target directory name.

# NOTE: This will only work if `GITHUB_REF` is defined in the environment; this
# is the case in GitHub actions.

github_ref = os.environ.get("GITHUB_REF")
if github_ref == "refs/heads/master":
    target = "master"
elif github_ref.startswith("refs/tags/"):
    # Matches vx.y or vx.y.z
    m = re.match(r"^refs/tags/v([0-9]+\.[0-9]+(?:\.[0-9]+)?)$", github_ref)
    target = m.group(1)
else:
    # TODO: This should be the empty string, after testing.
    target = "test-version"
print(f'echo "target={target}" >> $GITHUB_OUTPUT')
