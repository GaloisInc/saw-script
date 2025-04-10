# Deprecated Items

:::{warning}
This section is under construction!
:::

- `addsimp' : Term -> Simpset -> Simpset`
- `addsimps' : [Term] -> Simpset -> Simpset`

  These functions unconditionally added rules represented as `Term` values to a
  `Simpset`.
  When used in a proof, these functions make the correctness of the added rules
  a side condition of the proof process's soundness.
