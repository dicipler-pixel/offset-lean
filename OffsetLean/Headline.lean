import OperatorFirst.OffsetEndpoint
import OperatorFirst.EndpointTransfer
import OperatorFirst.FiniteCovariance
import OperatorFirst.BandObstruction
import OperatorFirst.LaurentBoundary

/-!
# The Offset Belongs to the Boundary — headline results

Each statement below is written using only Lean core and Mathlib notions
(real and complex numbers, `Real.log`, `Real.tanh`, matrices, determinants,
polynomials, Laurent polynomials, limits). No definition from this project is
needed to read them. Each one is proved by citing the corresponding theorem of
the library in `OperatorFirst/`, so trusting this file means trusting those
proofs and the Lean kernel, nothing else.

What these statements do NOT say is recorded in `LIMITATIONS.md`: no
infinite-chain Rice–Mele limit, no energy calibration, no spacetime metric and
no cosmological-constant value is proved here.

Throughout, `p` is the full-block probability `det C` and `m` the empty-block
probability `det(1 - C)`, so `(m - p) / (m + p)` is their asymmetry and
`log m - log p = Tr K_A` is the offset.
-/

open Filter

namespace OffsetLean.Headline

/-- **Asymmetry is the hyperbolic tangent of half the offset.**
For positive `p` and `m`, the normalised difference `(m - p) / (m + p)` equals
`tanh ((log m - log p) / 2)`. Library: `OffsetEndpoint.asymmetry_eq_tanh`. -/
theorem asymmetry_eq_tanh_half_offset (p m : ℝ) (hp : 0 < p) (hm : 0 < m) :
    (m - p) / (m + p) = Real.tanh ((Real.log m - Real.log p) / 2) :=
  OperatorFirst.OffsetEndpoint.asymmetry_eq_tanh p m hp hm

/-- **The endpoint amplitude stays strictly below one in the gapped regime.**
With band edges `emin² = (a - b)² + v²` and `emax² = (a + b)² + v²` and
positive hopping `b`, the normalised amplitude `v / √(emin · emax)` has
absolute value strictly less than one. Library: `OffsetEndpoint.gamma_lt_one`. -/
theorem endpoint_amplitude_lt_one (a b v emin emax : ℝ) (hb : 0 < b)
    (hemin : 0 < emin) (hemax : 0 < emax)
    (hmin : emin ^ 2 = (a - b) ^ 2 + v ^ 2)
    (hmax : emax ^ 2 = (a + b) ^ 2 + v ^ 2) :
    |v / Real.sqrt (emin * emax)| < 1 :=
  OperatorFirst.OffsetEndpoint.gamma_lt_one a b v emin emax hb hemin hemax hmin hmax

/-- **Relative errors move the asymmetry by at most `ε / (1 - ε)`.**
If each probability is perturbed by at most a fraction `ε < 1` of itself, the
asymmetry changes by at most `ε / (1 - ε)`.
Library: `EndpointTransfer.relative_error_bound`. -/
theorem asymmetry_relative_error {p m dp dm eps : ℝ}
    (hp : 0 < p) (hm : 0 < m) (he0 : 0 ≤ eps) (he1 : eps < 1)
    (hdp : |dp| ≤ eps * p) (hdm : |dm| ≤ eps * m) :
    |((m + dm) - (p + dp)) / ((m + dm) + (p + dp)) - (m - p) / (m + p)|
      ≤ eps / (1 - eps) :=
  OperatorFirst.EndpointTransfer.relative_error_bound hp hm he0 he1 hdp hdm

/-- **A compressed projector gives a strict formation domain.**
Let `P` be a real symmetric idempotent and `E` an isometric embedding
(`Eᵀ E = 1`). If both projected embeddings `P E` and `(1 - P) E` are
injective, then `C = Eᵀ P E` has `det C > 0`, `det (1 - C) > 0`, and the
determinant asymmetry lies strictly inside `(-1, 1)`.
Library: `FiniteCovariance.compression_formation_domain`. -/
theorem compression_formation_domain {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (P : Matrix ι ι ℝ) (E : Matrix ι κ ℝ)
    (hP : P.transpose = P) (hPP : P * P = P) (hE : E.transpose * E = 1)
    (hp : Function.Injective (P * E).mulVec)
    (hm : Function.Injective ((1 - P) * E).mulVec) :
    0 < (E.transpose * P * E).det ∧ 0 < (1 - E.transpose * P * E).det ∧
      |((1 - E.transpose * P * E).det - (E.transpose * P * E).det) /
          ((1 - E.transpose * P * E).det + (E.transpose * P * E).det)| < 1 :=
  OperatorFirst.FiniteCovariance.compression_formation_domain P E hP hPP hE hp hm

/-- **Bounded and convergent does not imply monotone.**
A tempting step in endpoint arguments is false: there is a real sequence
bounded by `1/2` in absolute value, converging to `1/2`, that is not monotone.
Library: `OffsetEndpoint.bounded_convergence_not_monotonicity`. -/
theorem bounded_convergent_not_monotone :
    ¬ (∀ a : ℕ → ℝ, (∀ n, |a n| ≤ 1 / 2) →
        Tendsto a atTop (nhds (1 / 2)) → Monotone a) :=
  OperatorFirst.OffsetEndpoint.bounded_convergence_not_monotonicity

/-- **An exact band cannot carry a nonzero polynomial vector.**
If the band equation and the dispersion relation hold on an infinite set of
complex numbers, with `a · b ≠ 0`, then both polynomial components vanish.
Library: `BandObstruction.polynomial_band_vector_zero`. -/
theorem band_equation_forces_zero (a b A v : ℂ) (hab : a * b ≠ 0)
    (U W : Polynomial ℂ) (E : ℂ → ℂ) (S : Set ℂ) (hS : S.Infinite)
    (hdisp : ∀ z ∈ S, z * (E z) ^ 2 =
      (Polynomial.C (a * b) * Polynomial.X ^ 2 + Polynomial.C A * Polynomial.X +
        Polynomial.C (a * b)).eval z)
    (hband : ∀ z ∈ S, z * E z * U.eval z = v * z * U.eval z - (a * z + b) * W.eval z) :
    U = 0 ∧ W = 0 :=
  OperatorFirst.BandObstruction.polynomial_band_vector_zero a b A v hab U W E S hS hdisp hband

/-- **One boundary column forces an affine polynomial.**
Take a square matrix of Laurent polynomials whose entries have no positive
powers except in one boundary column, where the top power is one. If its
determinant is `p(x)` for a polynomial `p`, evaluated through a ring map with no
positive powers and nonzero constant terms, at an `x` whose top power is exactly
one, then `p` has degree at most one.
Library: `LaurentBoundary.boundary_forces_polynomial_degree`. -/
theorem boundary_column_forces_affine {R S : Type*} [CommRing R] [CommRing S] [IsDomain S]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (LaurentPolynomial S)) (b : ι)
    (hbulk : ∀ i j, j ≠ b → ∀ k : ℤ, 0 < k → (M i j).coeff k = 0)
    (hboundary : ∀ i, ∀ k : ℤ, 1 < k → (M i b).coeff k = 0)
    (φ : R →+* LaurentPolynomial S) (hφ : ∀ a, ∀ k : ℤ, 0 < k → (φ a).coeff k = 0)
    (hφtop : ∀ a : R, a ≠ 0 → (φ a).coeff 0 ≠ 0)
    (x : LaurentPolynomial S) (hx : ∀ k : ℤ, 1 < k → x.coeff k = 0) (hx1 : x.coeff 1 ≠ 0)
    (p : Polynomial R) (hrepresentation : p.eval₂ φ x = M.det) :
    p.natDegree ≤ 1 :=
  OperatorFirst.LaurentBoundary.boundary_forces_polynomial_degree
    M b hbulk hboundary φ hφ hφtop x hx hx1 p hrepresentation

end OffsetLean.Headline
