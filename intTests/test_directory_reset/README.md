Test that a failed `include` leaves the current working directory, as printed by
`:pwd`, unchanged. Do this by `include`ing a bogus file outside the current
directory, bracketed with calls to `:pwd`, making sure that those calls produce
identical output, and that that output is the same as the initial working
directory.