# Isabelle Proof Checker
This tool checks proofterms of static facts of the given sessions.
It does not check dynamic facts, unnamed theorems, or theory extension.

- Install: `isabelle components -u <dir>`
- Usage (CLI): `isabelle check_build -?`
- Usage (interactive): see the [Example](test/Example.thy). Note that
  - background theory must be built with `record_proofs=2`
  - the `check_theory` commands trusts the current theories' ancestors