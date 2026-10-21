# Contributing

Issues and pull requests are welcome. We most want to hear about a statement that says something
other than what the Rust does, and about simpler proofs.

Two rules keep the results meaningful:

- Only the axioms `propext`, `Classical.choice` and `Quot.sound` are allowed. No `sorry`, no new
  `axiom`, and no `native_decide`, `decide +native` or `bv_decide`. H0 to H3 stay hypotheses. CI
  checks the axioms with `#print axioms`.
- The files listed in `FROZEN.sha256` are not edited in place, and no statement is weakened. A
  change to one of them is a new version, with new hashes.

The build must stay free of warnings in this package's own files. For commits and pull requests we
follow the [librustzcash style guides](https://github.com/zcash/librustzcash/blob/main/CONTRIBUTING.md#styleguides).

Changes meant for pasta_curves itself belong in that repository, under its own contribution
guidelines.
