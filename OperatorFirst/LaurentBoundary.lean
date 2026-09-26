import Mathlib

/-!
# The arbitrary-size boundary-column degree bound

Formal support bounds for Laurent polynomials and determinants. No size cutoff,
positivity assumption, or covariance interpretation is used. This module proves
the determinant-degree step of ALL_SIZE_TRANSFER.md; it does not assume the
physical sine law as an axiom.
-/

noncomputable section
open scoped BigOperators
open LaurentPolynomial

namespace OperatorFirst.LaurentBoundary

variable {R : Type*} [CommRing R]

/-- Every coefficient strictly above the integer bound is zero. -/
def Bounded (f : LaurentPolynomial R) (d : ℤ) : Prop :=
  ∀ k : ℤ, d < k → f.coeff k = 0

theorem bounded_zero (d : ℤ) : Bounded (0 : LaurentPolynomial R) d := by
  intro k hk
  simp

theorem bounded_mono {f : LaurentPolynomial R} {a b : ℤ}
    (hf : Bounded f a) (hab : a ≤ b) : Bounded f b := by
  intro k hk
  exact hf k (lt_of_le_of_lt hab hk)

theorem bounded_C (a : R) : Bounded (C a) 0 := by
  intro k hk
  simp [C_apply, ne_of_gt hk]

theorem bounded_monomial (a : R) (d : ℤ) : Bounded (C a * T d) d := by
  intro k hk
  rw [← single_eq_C_mul_T]
  change (Finsupp.single d a) k = 0
  exact Finsupp.single_eq_of_ne (ne_of_gt hk)

theorem bounded_add {f g : LaurentPolynomial R} {d : ℤ}
    (hf : Bounded f d) (hg : Bounded g d) : Bounded (f + g) d := by
  intro k hk
  simp [AddMonoidAlgebra.coeff_add, hf k hk, hg k hk]

theorem bounded_neg {f : LaurentPolynomial R} {d : ℤ}
    (hf : Bounded f d) : Bounded (-f) d := by
  intro k hk
  simp [AddMonoidAlgebra.coeff_neg, hf k hk]

theorem bounded_mul {f g : LaurentPolynomial R} {a b : ℤ}
    (hf : Bounded f a) (hg : Bounded g b) : Bounded (f * g) (a + b) := by
  classical
  intro k hk
  rw [AddMonoidAlgebra.coeff_mul_apply_left]
  apply Finset.sum_eq_zero
  intro i hi
  have hi' : f.coeff i ≠ 0 := Finsupp.mem_support_iff.mp hi
  have hia : i ≤ a := by
    by_contra hn
    exact hi' (hf i (lt_of_not_ge hn))
  change f.coeff i * g.coeff (-i + k) = 0
  rw [hg (-i + k) (by omega), mul_zero]

theorem bounded_sum {ι : Type*} (s : Finset ι)
    (f : ι → LaurentPolynomial R) (d : ℤ)
    (hf : ∀ i ∈ s, Bounded (f i) d) : Bounded (∑ i ∈ s, f i) d := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using bounded_zero (R := R) d
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact bounded_add (hf i (Finset.mem_insert_self i s))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem bounded_prod {ι : Type*} (s : Finset ι)
    (f : ι → LaurentPolynomial R) (d : ι → ℤ)
    (hf : ∀ i ∈ s, Bounded (f i) (d i)) :
    Bounded (∏ i ∈ s, f i) (∑ i ∈ s, d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using bounded_C (1 : R)
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact bounded_mul (hf i (Finset.mem_insert_self i s))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

/-- Each determinant term spends the degree budget of each column exactly once. -/
theorem determinant_column_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (LaurentPolynomial R)) (d : ι → ℤ)
    (hM : ∀ i j, Bounded (M i j) (d j)) :
    Bounded M.det (∑ j, d j) := by
  classical
  rw [Matrix.det_apply']
  apply bounded_sum
  intro σ hσ
  have hp := bounded_prod Finset.univ (fun j => M (σ j) j) d
    (fun j _ => hM (σ j) j)
  have hs : Bounded ((Equiv.Perm.sign σ : ℤ) : LaurentPolynomial R) 0 := by
    simpa using bounded_C ((Equiv.Perm.sign σ : ℤ) : R)
  simpa using bounded_mul hs hp

/-- One distinguished column allows at most degree one, in every finite size. -/
theorem determinant_one_boundary_column {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (LaurentPolynomial R)) (b : ι)
    (hbulk : ∀ i j, j ≠ b → Bounded (M i j) 0)
    (hboundary : ∀ i, Bounded (M i b) 1) : Bounded M.det 1 := by
  classical
  have h := determinant_column_bound M (fun j => if j = b then 1 else 0)
    (by intro i j; by_cases hj : j = b <;> simp [hj, hbulk, hboundary])
  simpa using h

/-- The same argument bounds growth by the number of degree-one boundary columns. -/
theorem determinant_boundary_set {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (LaurentPolynomial R)) (B : Finset ι)
    (hbulk : ∀ i j, j ∉ B → Bounded (M i j) 0)
    (hboundary : ∀ i j, j ∈ B → Bounded (M i j) 1) :
    Bounded M.det (B.card : ℤ) := by
  classical
  have h := determinant_column_bound M (fun j => if j ∈ B then 1 else 0)
    (by intro i j; by_cases hj : j ∈ B <;> simp [hj, hbulk, hboundary])
  simpa using h

/-- At the top possible exponent only the two top coefficients can contribute. -/
theorem coeff_mul_top {f g : LaurentPolynomial R} {a b : ℤ}
    (hf : Bounded f a) (hg : Bounded g b) :
    (f * g).coeff (a + b) = f.coeff a * g.coeff b := by
  classical
  rw [AddMonoidAlgebra.coeff_mul_apply_left]
  change (∑ i ∈ f.coeff.support, f.coeff i * g.coeff (-i + (a + b))) = _
  rw [Finset.sum_eq_single a]
  · simp
  · intro i hi hia
    by_cases hle : i ≤ a
    · have hlt : i < a := lt_of_le_of_ne hle hia
      rw [hg (-i + (a + b)) (by omega), mul_zero]
    · rw [hf i (lt_of_not_ge hle), zero_mul]
  · intro ha
    rw [Finsupp.notMem_support_iff.mp ha, zero_mul]

theorem bounded_pow_one {f : LaurentPolynomial R} (hf : Bounded f 1) (n : ℕ) :
    Bounded (f ^ n) (n : ℤ) := by
  induction n with
  | zero => simpa using bounded_C (1 : R)
  | succ n ih =>
    simpa [pow_succ, Nat.cast_add, Nat.cast_one] using bounded_mul ih hf

theorem coeff_pow_top {f : LaurentPolynomial R} (hf : Bounded f 1) (n : ℕ) :
    (f ^ n).coeff (n : ℤ) = (f.coeff 1) ^ n := by
  induction n with
  | zero => simpa using (LaurentPolynomial.C_apply (1 : R) (0 : ℤ))
  | succ n ih =>
    simpa [pow_succ, Nat.cast_add, Nat.cast_one, ih] using
      (coeff_mul_top (bounded_pow_one hf n) hf)

section PolynomialDescent

variable {S : Type*} [CommRing S]

/-- A coefficient substitution of degree at most zero cannot increase the
    degree supplied by the substituted polynomial variable. -/
theorem bounded_eval₂ (φ : R →+* LaurentPolynomial S)
    (hφ : ∀ a, Bounded (φ a) 0) (x : LaurentPolynomial S)
    (hx : Bounded x 1) (p : Polynomial R) :
    Bounded (p.eval₂ φ x) (p.natDegree : ℤ) := by
  classical
  rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  apply bounded_sum
  intro k hk
  have hk' : k ≤ p.natDegree :=
    Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hk)
  have h := bounded_mul (hφ (p.coeff k)) (bounded_pow_one hx k)
  exact bounded_mono (by simpa using h) (by exact_mod_cast hk')

/-- The leading coefficient survives the substitution exactly; no lower
    polynomial degree can contribute at this Laurent exponent. -/
theorem coeff_eval₂_top (φ : R →+* LaurentPolynomial S)
    (hφ : ∀ a, Bounded (φ a) 0) (x : LaurentPolynomial S)
    (hx : Bounded x 1) (p : Polynomial R) :
    (p.eval₂ φ x).coeff (p.natDegree : ℤ) =
      (φ p.leadingCoeff).coeff 0 * (x.coeff 1) ^ p.natDegree := by
  classical
  rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  simp only [AddMonoidAlgebra.coeff_sum]
  rw [Finset.sum_apply']
  rw [Finset.sum_eq_single p.natDegree]
  · simpa [Polynomial.coeff_natDegree, coeff_pow_top hx] using
      coeff_mul_top (hφ (p.coeff p.natDegree)) (bounded_pow_one hx p.natDegree)
  · intro k hk hkm
    have hk' : k ≤ p.natDegree :=
      Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hk)
    have h := bounded_mul (hφ (p.coeff k)) (bounded_pow_one hx k)
    exact h (p.natDegree : ℤ) (by omega)
  · intro hm
    have hz : p.coeff p.natDegree = 0 := Polynomial.notMem_support_iff.mp hm
    simp [hz]

/-- This is the no-cancellation descent in the all-size written proof.
    The injectivity requirement on coefficient constants is explicit. -/
theorem polynomial_degree_le_one [IsDomain S]
    (φ : R →+* LaurentPolynomial S) (hφ : ∀ a, Bounded (φ a) 0)
    (hφtop : ∀ a : R, a ≠ 0 → (φ a).coeff 0 ≠ 0)
    (x : LaurentPolynomial S) (hx : Bounded x 1) (hx1 : x.coeff 1 ≠ 0)
    (p : Polynomial R) (hdet : Bounded (p.eval₂ φ x) 1) :
    p.natDegree ≤ 1 := by
  by_cases hp : p = 0
  · simp [hp]
  by_contra hdeg
  have hgt : (1 : ℤ) < (p.natDegree : ℤ) := by omega
  have hz := hdet (p.natDegree : ℤ) hgt
  rw [coeff_eval₂_top φ hφ x hx p] at hz
  exact (mul_ne_zero (hφtop p.leadingCoeff (Polynomial.leadingCoeff_ne_zero.mpr hp))
    (pow_ne_zero p.natDegree hx1)) hz

/-- An explicit determinant representation with one boundary column and a
    faithful leading-coefficient chart forces degree at most one. -/
theorem boundary_forces_polynomial_degree [IsDomain S]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (LaurentPolynomial S)) (b : ι)
    (hbulk : ∀ i j, j ≠ b → Bounded (M i j) 0)
    (hboundary : ∀ i, Bounded (M i b) 1)
    (φ : R →+* LaurentPolynomial S) (hφ : ∀ a, Bounded (φ a) 0)
    (hφtop : ∀ a : R, a ≠ 0 → (φ a).coeff 0 ≠ 0)
    (x : LaurentPolynomial S) (hx : Bounded x 1) (hx1 : x.coeff 1 ≠ 0)
    (p : Polynomial R) (hrepresentation : p.eval₂ φ x = M.det) :
    p.natDegree ≤ 1 := by
  apply polynomial_degree_le_one φ hφ hφtop x hx hx1 p
  rw [hrepresentation]
  exact determinant_one_boundary_column M b hbulk hboundary

/-- Degree at most one gives the literal affine polynomial, including constants
    and zero. Coefficients are fixed by the polynomial, not chosen pointwise. -/
theorem polynomial_affine_of_degree (p : Polynomial R) (hp : p.natDegree ≤ 1) :
    p = Polynomial.C (p.coeff 0) + Polynomial.C (p.coeff 1) * Polynomial.X := by
  ext n
  rcases n with _ | n
  · simp
  rcases n with _ | n
  · simp
  have hz : p.coeff (n + 1 + 1) = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  simp [hz, Polynomial.coeff_mul_X]

end PolynomialDescent

end OperatorFirst.LaurentBoundary

#print axioms OperatorFirst.LaurentBoundary.bounded_zero
#print axioms OperatorFirst.LaurentBoundary.bounded_mono
#print axioms OperatorFirst.LaurentBoundary.bounded_C
#print axioms OperatorFirst.LaurentBoundary.bounded_monomial
#print axioms OperatorFirst.LaurentBoundary.bounded_add
#print axioms OperatorFirst.LaurentBoundary.bounded_neg
#print axioms OperatorFirst.LaurentBoundary.bounded_mul
#print axioms OperatorFirst.LaurentBoundary.bounded_sum
#print axioms OperatorFirst.LaurentBoundary.bounded_prod
#print axioms OperatorFirst.LaurentBoundary.determinant_column_bound
#print axioms OperatorFirst.LaurentBoundary.determinant_one_boundary_column
#print axioms OperatorFirst.LaurentBoundary.determinant_boundary_set
#print axioms OperatorFirst.LaurentBoundary.coeff_mul_top
#print axioms OperatorFirst.LaurentBoundary.bounded_pow_one
#print axioms OperatorFirst.LaurentBoundary.coeff_pow_top
#print axioms OperatorFirst.LaurentBoundary.bounded_eval₂
#print axioms OperatorFirst.LaurentBoundary.coeff_eval₂_top
#print axioms OperatorFirst.LaurentBoundary.polynomial_degree_le_one
#print axioms OperatorFirst.LaurentBoundary.boundary_forces_polynomial_degree

#print axioms OperatorFirst.LaurentBoundary.polynomial_affine_of_degree
