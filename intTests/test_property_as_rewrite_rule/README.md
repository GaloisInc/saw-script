This tests limited automatic unfolding in `addsimp*`. Rather than unwrap
`XorInvolutes` into its functional definition at the `prove*` site, we can prove
the property by name and include its *immediate* definition as the rewrite rule.
No further unwrapping takes place.