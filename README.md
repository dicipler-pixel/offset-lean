<div align="center">

# The Offset Belongs to the Boundary — Lean proofs

**Machine-checked finite algebra behind the entanglement offset of a gapped free-fermion chain.**

[![Lean proof check](https://github.com/dicipler-pixel/offset-lean/actions/workflows/build.yml/badge.svg)](https://github.com/dicipler-pixel/offset-lean/actions/workflows/build.yml)
![Lean](https://img.shields.io/badge/Lean-v4.33.0-blue)
![Theorems](https://img.shields.io/badge/theorems-143_%2B_7_headline-2EA043)
![sorry](https://img.shields.io/badge/sorry-0-2EA043)
![License](https://img.shields.io/badge/License-MIT-lightgrey)
[![Paper DOI](https://img.shields.io/badge/paper-10.5281%2Fzenodo.22555919-blue)](https://doi.org/10.5281/zenodo.22555919)

Jeromie Beasley

</div>

---

## The idea in one line

Cut a block out of a gapped chain of fermions. The trace of its entanglement
Hamiltonian, the **offset**, is the log-odds of finding the block completely
empty versus completely full:

$$
\operatorname{Tr} K_A \;=\; \log \det(1 - C_A) \;-\; \log \det C_A \;=\; \log P(\text{empty}) - \log P(\text{full}),
\qquad
\frac{P(\text{full}) - P(\text{empty})}{P(\text{full}) + P(\text{empty})} \;=\; \tanh\!\left(\frac{\text{offset}}{2}\right).
$$

The paper measures this number, shows that a symmetry of the cut arrangement
forces it to vanish, and recognises a closed form for it across the Rice–Mele
family (matched numerically; its derivation is still open). This repository proves, in Lean 4 with Mathlib, the finite
algebra that argument stands on. Every proof is checked by the Lean kernel on
every push.

## Start here

| If you want to… | Open |
| :--- | :--- |
| See the main results in plain Mathlib terms | [`OffsetLean/Headline.lean`](OffsetLean/Headline.lean) |
| Know exactly what is **not** proved | [`LIMITATIONS.md`](LIMITATIONS.md) |
| Check where every file came from | [`PROVENANCE.md`](PROVENANCE.md) |
| See the proofs themselves | [`OperatorFirst/`](OperatorFirst/) |
| See the statements that must be rejected | [`FalseControls/`](FalseControls/) |

## Headline results

Seven statements, each written using only Lean core and Mathlib notions, so
no definition from this project is needed to read them. Each is proved by
citing a theorem in the library.

| # | Statement | In words |
| :-: | :--- | :--- |
| 1 | `asymmetry_eq_tanh_half_offset` | For positive `p, m`: `(m − p)/(m + p) = tanh((log m − log p)/2)` |
| 2 | `endpoint_amplitude_lt_one` | With positive hopping, the endpoint amplitude `v / √(Emin·Emax)` is strictly inside `(−1, 1)` |
| 3 | `asymmetry_relative_error` | Perturbing each probability by at most a fraction `ε < 1` moves the asymmetry by at most `ε/(1 − ε)` |
| 4 | `compression_formation_domain` | A compressed symmetric projector with both projected embeddings injective gives `det C > 0`, `det(1 − C) > 0`, asymmetry inside `(−1, 1)` |
| 5 | `bounded_convergent_not_monotone` | Bounded and convergent does **not** imply monotone (a false step, refuted) |
| 6 | `band_equation_forces_zero` | An exact band equation on infinitely many points forces both polynomial components to vanish |
| 7 | `boundary_column_forces_affine` | A determinant with a single boundary column of top degree one is an affine polynomial |

## What the library contains

The proof files keep their original module names so their hashes match the
verified sources exactly. Grouped by subject:

| Subject | Files | Theorems |
| :--- | :--- | :-: |
| **The offset as log-odds**: occupations, flip symmetry, finite log-odds of empty versus full, determinant ratios, counterexamples to over-reaching claims | `Offset`, `OffsetFock` | 53 |
| **Reflection and the endpoint formula**: sublattice reflection, the offset is minus twice the odd part, asymmetry = tanh(offset/2), strict band products, refuted monotonicity | `OffsetEndpoint` | 30 |
| **Transfer and error control**: three-site interpolation, transfer mixing, relative-error bounds, conditional endpoint assembly | `EndpointProgress`, `EndpointTransfer` | 25 |
| **Finite covariance and band obstruction**: compressed projectors are Gram matrices, strict formation domain, exact band forces zero | `FiniteCovariance`, `BandObstruction` | 11 |
| **Boundary-column degree mechanism**: Laurent coefficient bounds, determinant column budgets, one boundary column forces an affine polynomial | `LaurentBoundary` | 20 |
| **Rice–Mele sign symmetry**: flipping every B-sublattice site sends hopping signs `(a, b) → (−a, −b)` and leaves the determinant unchanged | `RiceMeleOddSymmetry` | 4 |
| | **Total** | **143** |

## How it is checked

Every push runs [the proof check](.github/workflows/build.yml) on GitHub:

1. **Build**: every module compiles against Lean v4.33.0 and Mathlib `v4.33.0`.
2. **Independent replay**: every module is re-checked by Lean's separate kernel checker.
3. **Axiom audit**: every one of the 150 named theorems depends only on
   `propext`, `Classical.choice` and `Quot.sound`, the three standard axioms
   of Mathlib. No `sorry`, no project axioms, no `native_decide`.
4. **False controls**: 13 deliberately false statements must fail to compile,
   and fail for a mathematical reason, not a typo. This shows the checker can say no.

The evidence (axiom log, control logs, `report.json` with the SHA-256 of every
file) is attached to each run.

To check it yourself with Lean installed:

```bash
lake exe cache get
lake build
python3 scripts/verify.py
```

## Scope

Lean proves exactly the statements written, under exactly the hypotheses
written. The infinite-chain limit, the closed form's derivation, energy
calibration and any cosmological reading are **outside** these proofs; see
[`LIMITATIONS.md`](LIMITATIONS.md) for the complete list.

## The paper

*The Offset Belongs to the Boundary*, Jeromie Beasley. DOI [10.5281/zenodo.22555919](https://doi.org/10.5281/zenodo.22555919).

## Citation, licence and AI use

Citation metadata is in [`CITATION.cff`](CITATION.cff). The Lean code and
scripts are released under the [MIT License](LICENSE); prose and figures under
CC BY 4.0. How AI tools were used is stated in [`AI_USE.md`](AI_USE.md).
