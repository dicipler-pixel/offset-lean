import OperatorFirst.LaurentBoundary
import Mathlib.Data.Complex.Basic

/-!
# The explicit odd-boundary Laurent matrix

Equation (9) of ALL_SIZE_TRANSFER.md, at arbitrary finite size. This file
supplies entry bounds for the actual displayed matrix, rather than assuming
those bounds. The invariant-polynomial representation is a separate obligation.
-/
noncomputable section
open LaurentPolynomial
open OperatorFirst.LaurentBoundary

namespace OperatorFirst.BoundaryModel

abbrev L := LaurentPolynomial ℂ
abbrev Index (n : ℕ) := Fin n ⊕ (Fin n ⊕ Unit)

def mon (z : ℂ) (d : ℤ) : L := AddMonoidAlgebra.single d z

structure Data (n : ℕ) where
  H : Matrix (Fin n) (Fin n) ℂ
  G : Matrix (Fin n) (Fin n) ℂ
  K : Matrix (Fin n) (Fin n) ℂ
  eta : Fin n → ℂ
  gamma : Fin n → ℂ
  zeta : Fin n → ℂ
  h0 : ℂ
  g0 : ℂ

/-- All nine blocks of the displayed transformed matrix. -/
def transformed {n : ℕ} (d : Data n) (p c : ℂ) : Matrix (Index n) (Index n) L
  | .inl i, .inl j =>
      mon (d.H i j) 0 + mon (Complex.I*p*(d.K i j-d.K j i)/2) (-1)
  | .inl i, .inr (.inl j) =>
      mon (-2*Complex.I*d.G i j) 0 +
      mon (-(c*d.G i j+Complex.I*p*(d.K i j+d.K j i)/2)) (-2)
  | .inl i, .inr (.inr _) =>
      mon (d.eta i/2) 0 + mon (-Complex.I*d.gamma i) 1 +
      mon (-(c*d.gamma i+Complex.I*p*d.zeta i)/2) (-1)
  | .inr (.inl i), .inl j =>
      mon (-c*d.G i j+Complex.I*p*(d.K i j+d.K j i)/2) 0
  | .inr (.inl i), .inr (.inl j) =>
      mon (d.H i j) 0 + mon (-Complex.I*p*(d.K i j-d.K j i)/2) (-1)
  | .inr (.inl i), .inr (.inr _) =>
      mon (d.eta i/2) 1 + mon ((-c*d.gamma i+Complex.I*p*d.zeta i)/2) 0
  | .inr (.inr _), .inl j =>
      mon (d.eta j) 0 + mon (-c*d.gamma j+Complex.I*p*d.zeta j) (-1)
  | .inr (.inr _), .inr (.inl j) =>
      mon (d.eta j) (-1) + mon (-2*Complex.I*d.gamma j) 0 +
      mon (-(c*d.gamma j+Complex.I*p*d.zeta j)) (-2)
  | .inr (.inr _), .inr (.inr _) =>
      mon d.h0 0 + mon (-Complex.I*d.g0) 1 + mon (-c*d.g0) (-1)

theorem mon_bounded (z : ℂ) (a b : ℤ) (h : a ≤ b) : Bounded (mon z a) b :=
  by simpa only [mon, single_eq_C_mul_T] using bounded_mono (bounded_monomial z a) h

/-- The concrete ordinary columns have no positive Laurent exponents. -/
theorem transformed_bulk_bound {n : ℕ} (d : Data n) (p c : ℂ)
    (i j : Index n) (hj : j ≠ .inr (.inr ())) :
    Bounded (transformed d p c i j) 0 := by
  rcases i with i | (i | i) <;> rcases j with j | (j | j)
  all_goals try { cases j; exact (hj rfl).elim }
  all_goals simp only [transformed]
  all_goals repeat' first | apply bounded_add | exact mon_bounded _ _ _ (by norm_num)

/-- The single boundary column has upper exponent at most one. -/
theorem transformed_boundary_bound {n : ℕ} (d : Data n) (p c : ℂ)
    (i : Index n) : Bounded (transformed d p c i (.inr (.inr ()))) 1 := by
  rcases i with i | (i | i)
  all_goals simp only [transformed]
  all_goals repeat' first | apply bounded_add | exact mon_bounded _ _ _ (by norm_num)

/-- No size cutoff or assumed entry bounds: the explicit matrix has degree ≤ 1. -/
theorem transformed_determinant_bound {n : ℕ} (d : Data n) (p c : ℂ) :
    Bounded (transformed d p c).det 1 := by
  apply determinant_one_boundary_column (transformed d p c) (.inr (.inr ()))
  · exact transformed_bulk_bound d p c
  · exact transformed_boundary_bound d p c

/-- The written onsite chart has precisely its asserted upper degree. -/
def onsite (c : ℂ) : L := mon Complex.I 1 + mon c (-1)

theorem onsite_bound (c : ℂ) : Bounded (onsite c) 1 := by
  exact bounded_add (mon_bounded _ _ _ (by norm_num)) (mon_bounded _ _ _ (by norm_num))

theorem onsite_top (c : ℂ) : (onsite c).coeff 1 = Complex.I := by
  simp [onsite, mon, ← single_eq_C_mul_T]

theorem onsite_top_ne_zero (c : ℂ) : (onsite c).coeff 1 ≠ 0 := by
  rw [onsite_top]
  exact Complex.I_ne_zero


/-- The substituted original matrix in paired A/B/boundary order, equation (8). -/
def original {n : ℕ} (d : Data n) (p c : ℂ) : Matrix (Index n) (Index n) L
  | .inl i, .inl j => mon (d.H i j) 0 + mon (-Complex.I*d.G i j) 1 + mon (-c*d.G i j) (-1)
  | .inl i, .inr (.inl j) => mon (d.G i j) 1 + mon (p*d.K i j) (-1)
  | .inl i, .inr (.inr _) => mon (d.eta i) 0 + mon (-Complex.I*d.gamma i) 1 + mon (-c*d.gamma i) (-1)
  | .inr (.inl i), .inl j => mon (d.G i j) 1 + mon (p*d.K j i) (-1)
  | .inr (.inl i), .inr (.inl j) => mon (d.H i j) 0 + mon (Complex.I*d.G i j) 1 + mon (c*d.G i j) (-1)
  | .inr (.inl i), .inr (.inr _) => mon (d.gamma i) 1 + mon (p*d.zeta i) (-1)
  | .inr (.inr _), .inl j => mon (d.eta j) 0 + mon (-Complex.I*d.gamma j) 1 + mon (-c*d.gamma j) (-1)
  | .inr (.inr _), .inr (.inl j) => mon (d.gamma j) 1 + mon (p*d.zeta j) (-1)
  | .inr (.inr _), .inr (.inr _) => mon d.h0 0 + mon (-Complex.I*d.g0) 1 + mon (-c*d.g0) (-1)

/-- U D, with D rescaling only the second paired sector. -/
def basis (n : ℕ) : Matrix (Index n) (Index n) L
  | .inl i, .inl j => if i=j then mon 1 0 else 0
  | .inl i, .inr (.inl j) => if i=j then mon 1 (-1) else 0
  | .inr (.inl i), .inl j => if i=j then mon Complex.I 0 else 0
  | .inr (.inl i), .inr (.inl j) => if i=j then mon (-Complex.I) (-1) else 0
  | .inr (.inr _), .inr (.inr _) => 1
  | _, _ => 0

/-- D⁻¹ U⁻¹, expressed without an abstract inverse. -/
def basisInv (n : ℕ) : Matrix (Index n) (Index n) L
  | .inl i, .inl j => if i=j then mon (1/2) 0 else 0
  | .inl i, .inr (.inl j) => if i=j then mon (-Complex.I/2) 0 else 0
  | .inr (.inl i), .inl j => if i=j then mon (1/2) 1 else 0
  | .inr (.inl i), .inr (.inl j) => if i=j then mon (Complex.I/2) 1 else 0
  | .inr (.inr _), .inr (.inr _) => 1
  | _, _ => 0

theorem mon_mul (a b : ℂ) (j k : ℤ) : mon a j * mon b k = mon (a*b) (j+k) := by
  simp only [mon, AddMonoidAlgebra.single_mul_single]


/-- The explicit change of basis is an inverse on the left. -/
theorem basis_inverse (n : ℕ) : basisInv n * basis n = 1 := by
  ext i j
  rcases i with i | (i | i) <;> rcases j with j | (j | j)
  all_goals simp [Matrix.mul_apply, Fintype.sum_sum_type, basisInv, basis,
    mon_mul, Matrix.one_apply]
  all_goals simp only [mon, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  all_goals (try split_ifs) <;> ring_nf <;> simp [Complex.I_sq]
  all_goals try simp only [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  all_goals (try split_ifs) <;> first | omega | ring

/-- Equation (9), with arbitrary block size and no entry-bound hypotheses. -/
theorem explicit_similarity {n : ℕ} (d : Data n) (p c : ℂ) :
    basisInv n * original d p c * basis n = transformed d p c := by
  ext i j
  rcases i with i | (i | i) <;> rcases j with j | (j | j)
  all_goals simp [Matrix.mul_apply, Fintype.sum_sum_type, basisInv, basis,
    original, transformed, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum,
    add_mul, mul_add, mon_mul]
  all_goals simp only [mon, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  all_goals (try split_ifs) <;> ring_nf <;> simp [Complex.I_sq]
  all_goals try simp only [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  all_goals (try split_ifs) <;> first | omega | ring


/-- Similarity transports the explicit determinant bound back to equation (8). -/
theorem original_determinant_bound {n : ℕ} (d : Data n) (p c : ℂ) :
    Bounded (original d p c).det 1 := by
  have hb := congrArg Matrix.det (basis_inverse n)
  simp only [Matrix.det_mul, Matrix.det_one] at hb
  have hs := congrArg Matrix.det (explicit_similarity d p c)
  simp only [Matrix.det_mul] at hs
  have he : (original d p c).det = (transformed d p c).det := by
    calc
      (original d p c).det =
          ((basisInv n).det * (basis n).det) * (original d p c).det := by rw [hb, one_mul]
      _ = (transformed d p c).det := by rw [← hs]; ring
  rw [he]
  exact transformed_determinant_bound d p c


/-- The physical dispersion invariant after the actual Laurent substitution. -/
theorem chart_dispersion (p c : ℂ) :
    mon 1 1 ^ 2 + mon p (-1) ^ 2 + onsite c ^ 2 =
      mon (2*Complex.I*c) 0 + mon (c^2+p^2) (-2) := by
  simp only [onsite, pow_two, add_mul, mul_add, mon_mul]
  ext k
  simp only [mon, AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_single,
    Finsupp.single_apply]
  norm_num
  simp only [Finsupp.single_apply]
  split_ifs <;> ring_nf <;> simp [Complex.I_sq] <;> ring

theorem chart_dispersion_bound (p c : ℂ) :
    Bounded (mon 1 1 ^ 2 + mon p (-1) ^ 2 + onsite c ^ 2) 0 := by
  rw [chart_dispersion]
  exact bounded_add (mon_bounded _ _ _ (by norm_num)) (mon_bounded _ _ _ (by norm_num))

end OperatorFirst.BoundaryModel


#print axioms OperatorFirst.BoundaryModel.mon_bounded
#print axioms OperatorFirst.BoundaryModel.transformed_bulk_bound
#print axioms OperatorFirst.BoundaryModel.transformed_boundary_bound
#print axioms OperatorFirst.BoundaryModel.transformed_determinant_bound
#print axioms OperatorFirst.BoundaryModel.onsite_bound
#print axioms OperatorFirst.BoundaryModel.onsite_top
#print axioms OperatorFirst.BoundaryModel.onsite_top_ne_zero
#print axioms OperatorFirst.BoundaryModel.mon_mul
#print axioms OperatorFirst.BoundaryModel.basis_inverse
#print axioms OperatorFirst.BoundaryModel.explicit_similarity
#print axioms OperatorFirst.BoundaryModel.original_determinant_bound
#print axioms OperatorFirst.BoundaryModel.chart_dispersion
#print axioms OperatorFirst.BoundaryModel.chart_dispersion_bound
