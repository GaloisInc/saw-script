# The counterexample value generated isn't stable, which is not
# particularly surprising. Replace it with NNN.

awk '
   # look only between the horizontal counterexample bars
   /^ ------/ { look = !look }
   look { sub("x: [0-9]+", "x: NNN", $0) }
   { print }
' | sed 's,\(solverStatsGoalSize.=.\)[0-9N]*,\1N,g'
