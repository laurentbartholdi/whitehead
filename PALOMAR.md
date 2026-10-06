# Palomar preparation

The proof package is mechanically ready for a hosted Palomar preflight:

- `comparator.json` compares `Whitehead.TheoremA` in `Challenge` and `Solution`.
- The permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- The local Comparator run passed Lean's kernel and NanoDa. Because macOS lacks
  Comparator's Linux `bwrap` sandbox, that run used
  `--inadvisably-no-sandbox`; its log is `verification/comparator-local-rc3.log`.
- `.github/workflows/palomar-preflight.yml` pins the current Palomar verifier
  commit and computes a valid 12-character request ID.
- Lean and mathlib are pinned to `v4.35.0-rc3`, above Palomar's current minimum
  `v4.35.0-rc2`.

The package uses the Apache-2.0 license declared in `formalization.yaml`.
Commit it in the public GitHub repository and run the workflow against that
exact 40-character commit SHA. The workflow is a preflight only and does not
submit the result.
