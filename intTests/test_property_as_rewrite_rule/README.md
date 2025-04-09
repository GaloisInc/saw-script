This tests limited automatic unfolding in `addsimp*`. Rather than manually
unwrap `XorInvolutes` into its functional definition at the `prove*` site in
SAW, we can prove the property by name and include its *immediate* definition as
the rewrite rule. No further unwrapping takes place, since `XorInvolutes`
unfolds to a well-formed simplification rule.
