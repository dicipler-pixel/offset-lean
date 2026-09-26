# Limitations

Stated so a reader can calibrate exactly what the Lean proofs establish.

## What is proved

Finite algebra and conditional limit statements: exactly the 143 library
theorems and 7 headline theorems in this repository, under exactly the
hypotheses written in each statement. Every one depends only on `propext`,
`Classical.choice` and `Quot.sound`. There is no `sorry`, no project-defined
axiom and no `native_decide` anywhere in `OperatorFirst/` or `OffsetLean/`.

These are 143 formal statements, not 143 independent physical results. Several
are deliberate counterexamples that refute tempting but false inferences.

## What is not proved here

1. **The infinite-chain limit.** No Rice–Mele endpoint limit is proved. The
   target, for positive hopping in the strict gapped regime on odd blocks, is
   `|Ω_L(v)| → artanh(|v| / √(Emin·Emax))`. The library proves the amplitude is
   strictly below one and that the limit follows **if** the transfer and
   convergence premises are supplied (`endpoint_of_approximate_transfer`).
   It does not supply them.
2. **The closed form.** `|Tr K_A| = 2 artanh(v / √(Emin·Emax))` is recognised
   and matched numerically in the paper. Its derivation is open, and it is not
   a Lean theorem.
3. **The infinite-chain operator.** The Rice–Mele Fourier operator is not
   constructed in Lean. Injectivity of its two finite-block projected
   embeddings is not derived from a Hamiltonian; the finite compression
   theorem takes injectivity as a hypothesis.
4. **All-size interpolation.** The unequal-hopping interpolation is formalised
   at three sites. The all-size version has a written proof in the paper. Lean
   has the general boundary-column mechanism (`LaurentBoundary`) but not the
   model-specific invariant-polynomial representation, block similarity or
   chart hypotheses.
5. **Hankel asymptotics.** The equal-hopping Fourier/Hankel reduction and its
   asymptotic theorem are not formalised.
6. **Physical interpretation.** The determinant formulas are algebraic
   identities about logarithms of determinants. Their reading as Gaussian-state
   probabilities or as a matrix-logarithm trace rests on state and spectral
   identifications that are not formalised here.
7. **Signs and rates.** A signed limit along all odd sizes is not claimed.
   Geometric convergence, monotonicity, an exact rate, uniform convergence and
   failure of uniformity at criticality are not established by these finite
   lemmas.
8. **Calibration and cosmology.** No energy calibration, spacetime metric,
   Abel-map phase, interior ladder spacing or cosmological-constant value is
   assumed or derived.

## Counterexamples kept on purpose

Some theorems exist to block a wrong step:

- Reflection symmetry alone does not bound growth: a logistic family has
  reflection symmetry and offset growing linearly (`reflection_allows_linear_growth`).
- Nonzero hopping alone does not make the band product strict: it fails at a
  gap-closing point (`critical_counterexample`).
- Bounded and convergent does not imply monotone (`bounded_convergence_not_monotonicity`).
- A shear with determinant one still fails the parity-eigenvector claim
  (`plus_parity_not_eigenvector`).

The `FalseControls/` folder holds 13 statements that must fail to compile.

## Review status

The development was produced with AI assistance (see `AI_USE.md`) and checked
by the Lean kernel and an independent kernel replay. It has not been
refereed. No claim is made that these statements have not been formalised
elsewhere.
