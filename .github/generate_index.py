#!/usr/bin/env python3

# This script generates an HTML index file for all coverage reports

import glob

HEADER = """
<!DOCTYPE html>
<head>
  <title>SAWScript Test Coverage Results</title>
</head>
<body>
  <h1>SAWScript Test Coverage Results</h1>
  <p>SAWScript coverage results by pull request number:</p>
  <ul>
"""

FOOTER = """
  </ul>
</body>
"""

if __name__ == "__main__":
  with open("index.html", "w") as f:
    f.write(HEADER)
    for dir in sorted(glob.glob("coverage-html-*")):
      pr_num = dir[14:]
      link_dest = f"{dir}/hpc_index.html"
      f.write(f"    <li><a href={link_dest}>{pr_num}</a></li>")
    f.write(FOOTER)
