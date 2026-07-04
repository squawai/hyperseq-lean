# Hypersequent Calculi — Lean 4 Formalizations

Lean 4 formalizations of hypersequent calculi for various logics, each
independent of any single paper. This repository is **self-contained**:
no Mathlib dependency, builds with `lake build` out of the box, and
every file can also be checked by pasting it into the
[Lean 4 web playground](https://live.lean-lang.org/).

## Contents

### `Modal/S5Hypersequent.lean`

A hypersequent calculus `HS5` for the modal logic **S5**, following the
Restall / Poggiolesi / Lahav pattern for modal hypersequents. Includes
Kripke semantics stubs (`S5Model`, `S5Force`, `S5Valid`, `S5HValid`).

Reference: A. Avron, "A constructive analysis of RM", *Journal of
Symbolic Logic* 52(4), 1987.

Status: definitions and calculus rules formalized, no `sorry`. Proofs
of soundness/completeness are future work.

### `FuzzyLogic/FuzzyHypersequent.lean`

Hypersequent calculi for fuzzy logics: **BL** (Basic Logic, `HBL`) and
**Łukasiewicz logic** (`HLuk`, extending `HBL` with the density rule).
`FuzzyFormula` adds a fusion connective (t-norm) alongside lattice
conjunction, with a residuated implication.

Reference: G. Metcalfe, N. Olivetti, D. Gabbay, *Proof Theory for
Fuzzy Logics*, Springer, 2009, Ch. 4–5.

Status: definitions and calculus rules formalized, no `sorry`. Proofs
of soundness/completeness are future work.

## Building

```sh
lake build
```

## License

MIT — see [LICENSE](./LICENSE).
