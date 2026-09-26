import Mathlib

/-!
# Model-specific symmetries of the odd Rice--Mele determinant block

This module begins the missing model-specific Lean layer in
`moduli_transfer/ALL_SIZE_TRANSFER.md`. It encodes the actual odd A/B block
and proves the simultaneous hopping-sign conjugacy used in the written proof.

It does not yet formalize the interval-reflection conjugacy, invariant-ring
reduction, Laurent block similarity, Fourier construction, or Hankel
asymptotics.
-/

noncomputable section
open scoped BigOperators
open Matrix

namespace OperatorFirst.RiceMeleOddSymmetry

variable {R : Type*} [CommRing R]

/-- Odd boundary index set `A₀,B₀,...,A_{n-1},B_{n-1},A_n`, represented as a
sum so the two sublattices keep their natural finite ranges. -/
abbrev Site (n : ℕ) := Sum (Fin (n+1)) (Fin n)

/-- Integer index difference used by the common Toeplitz coefficients. -/
def delta {m k : ℕ} (i : Fin m) (j : Fin k) : ℤ := (i.1 : ℤ) - (j.1 : ℤ)

/-- The structured `(2n+1)×(2n+1)` matrix from the all-size written proof.
No positivity, covariance, Fourier, or recurrence assumption is built in. -/
def oddBlock (n : ℕ) (g h : ℤ → R) (a b v : R) :
    Matrix (Site n) (Site n) R
  | Sum.inl i, Sum.inl j => h (delta i j) - v * g (delta i j)
  | Sum.inr i, Sum.inr j => h (delta i j) + v * g (delta i j)
  | Sum.inl i, Sum.inr j => a * g (delta i j) + b * g (delta i j - 1)
  | Sum.inr j, Sum.inl i => a * g (delta i j) + b * g (delta i j - 1)

/-- Sign attached to the B sublattice. -/
def bSign {n : ℕ} : Site n → R
  | Sum.inl _ => 1
  | Sum.inr _ => -1

/-- Diagonal matrix that flips every B basis vector. -/
def signMatrix (n : ℕ) : Matrix (Site n) (Site n) R :=
  Matrix.diagonal (bSign (R := R))

@[simp] theorem bSign_sq {n : ℕ} (i : Site n) :
    bSign (R := R) i * bSign (R := R) i = 1 := by
  cases i <;> simp [bSign]

/-- Flipping all B basis vectors changes `(a,b)` to `(-a,-b)` and leaves the
onsite parameter `v` unchanged. This is equation (4) of the written proof at
the matrix level. -/
theorem hopping_sign_conjugacy (n : ℕ) (g h : ℤ → R) (a b v : R) :
    signMatrix (R := R) n * oddBlock n g h a b v * signMatrix (R := R) n =
      oddBlock n g h (-a) (-b) v := by
  ext i j
  simp only [signMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal]
  cases i <;> cases j <;> simp [oddBlock, bSign] <;> ring

/-- The B-sign matrix is an involution. -/
theorem signMatrix_sq (n : ℕ) :
    signMatrix (R := R) n * signMatrix (R := R) n = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    cases i <;> simp [signMatrix, bSign]
  · simp [signMatrix, hij]

/-- Determinant form of the simultaneous hopping-sign symmetry:
`F(a,b,v)=F(-a,-b,v)` for every odd block size and arbitrary Toeplitz data. -/
theorem hopping_sign_det_invariant (n : ℕ) (g h : ℤ → R) (a b v : R) :
    (oddBlock n g h (-a) (-b) v).det = (oddBlock n g h a b v).det := by
  rw [← hopping_sign_conjugacy]
  rw [Matrix.det_mul, Matrix.det_mul]
  have hdet : (signMatrix (R := R) n).det * (signMatrix (R := R) n).det = 1 := by
    rw [← Matrix.det_mul, signMatrix_sq, Matrix.det_one]
  calc
    (signMatrix (R := R) n).det * (oddBlock n g h a b v).det *
        (signMatrix (R := R) n).det
        = (oddBlock n g h a b v).det *
          ((signMatrix (R := R) n).det * (signMatrix (R := R) n).det) := by ring
    _ = (oddBlock n g h a b v).det := by rw [hdet, mul_one]

end OperatorFirst.RiceMeleOddSymmetry

#print axioms OperatorFirst.RiceMeleOddSymmetry.bSign_sq
#print axioms OperatorFirst.RiceMeleOddSymmetry.hopping_sign_conjugacy
#print axioms OperatorFirst.RiceMeleOddSymmetry.signMatrix_sq
#print axioms OperatorFirst.RiceMeleOddSymmetry.hopping_sign_det_invariant
