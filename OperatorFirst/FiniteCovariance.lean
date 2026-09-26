import OperatorFirst.OffsetEndpoint

/-! Finite projection compression and the occupation domain.
The projection identities and the two injectivity hypotheses are explicit.
This module does not construct the infinite-chain Fourier projector. -/
noncomputable section
open Matrix
namespace OperatorFirst.FiniteCovariance
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

def compression (P : Matrix ι ι ℝ) (E : Matrix ι κ ℝ) : Matrix κ κ ℝ := Eᵀ*P*E

theorem compression_gram (P : Matrix ι ι ℝ) (E : Matrix ι κ ℝ)
    (hP : Pᵀ = P) (hPP : P*P = P) :
    compression P E = (P*E)ᵀ*(P*E) := by
  simp only [compression, transpose_mul, hP]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.mul_assoc Eᵀ P P, hPP]

theorem complement_projection (P : Matrix ι ι ℝ) (hPP : P*P = P) :
    (1-P)*(1-P) = 1-P := by
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hPP]
  abel

theorem complement_compression (P : Matrix ι ι ℝ) (E : Matrix ι κ ℝ)
    (hE : Eᵀ*E = 1) :
    compression (1-P) E = 1-compression P E := by
  simp only [compression, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hE]

theorem compression_posSemidef (P : Matrix ι ι ℝ) (E : Matrix ι κ ℝ)
    (hP : Pᵀ = P) (hPP : P*P = P) : (compression P E).PosSemidef := by
  rw [compression_gram P E hP hPP]
  simpa only [conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_conjTranspose_mul_self (P*E)

theorem compression_posDef (P : Matrix ι ι ℝ) (E : Matrix ι κ ℝ)
    (hP : Pᵀ = P) (hPP : P*P = P)
    (hinj : Function.Injective (P*E).mulVec) : (compression P E).PosDef := by
  rw [compression_gram P E hP hPP]
  simpa only [conjTranspose_eq_transpose_of_trivial] using
    Matrix.PosDef.conjTranspose_mul_self (P*E) hinj

/-- Occupied and empty injectivity are both required; idempotence alone only
gives semidefiniteness. E is an isometric finite-block embedding. -/
theorem compression_strict (P : Matrix ι ι ℝ) (E : Matrix ι κ ℝ)
    (hP : Pᵀ = P) (hPP : P*P = P) (hE : Eᵀ*E = 1)
    (hp : Function.Injective (P*E).mulVec)
    (hm : Function.Injective ((1-P)*E).mulVec) :
    (compression P E).PosDef ∧ (1-compression P E).PosDef := by
  refine ⟨compression_posDef P E hP hPP hp, ?_⟩
  rw [← complement_compression P E hE]
  apply compression_posDef (1-P) E _ (complement_projection P hPP) hm
  simp only [transpose_sub, transpose_one, hP]

theorem formation_determinants_positive (C : Matrix κ κ ℝ)
    (hp : C.PosDef) (hm : (1-C).PosDef) : 0 < C.det ∧ 0 < (1-C).det :=
  ⟨hp.det_pos, hm.det_pos⟩

/-- Every nonzero real eigenvector of a strict covariance has occupation in
(0,1). The eigenvalue equation is checked against the actual matrix. -/
theorem eigenvalue_in_unit_interval (C : Matrix κ κ ℝ)
    (hp : C.PosDef) (hm : (1-C).PosDef)
    (x : κ → ℝ) (hx : x ≠ 0) (nu : ℝ) (heig : C*ᵥx = nu • x) :
    0 < nu ∧ nu < 1 := by
  have hn : 0 < x ⬝ᵥ x := by
    simpa using (Matrix.PosDef.one (n := κ) (R := ℝ)).dotProduct_mulVec_pos hx
  have hp' := hp.dotProduct_mulVec_pos hx
  have hm' := hm.dotProduct_mulVec_pos hx
  have heig' : (1-C)*ᵥx = (1-nu) • x := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, heig]
    module
  rw [heig] at hp'
  rw [heig'] at hm'
  simp only [star_trivial, dotProduct_smul, smul_eq_mul] at hp' hm'
  constructor
  · by_contra h
    have := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) hn.le
    nlinarith
  · by_contra h
    have hn' : 1-nu ≤ 0 := by linarith
    have := mul_nonpos_of_nonpos_of_nonneg hn' hn.le
    nlinarith

def eigenOccupation (C : Matrix κ κ ℝ) (hp : C.PosDef) (hm : (1-C).PosDef)
    (x : κ → ℝ) (hx : x ≠ 0) (nu : ℝ) (heig : C*ᵥx = nu • x) : Offset.Occupation where
  nu := nu
  positive := (eigenvalue_in_unit_interval C hp hm x hx nu heig).1
  below_one := (eigenvalue_in_unit_interval C hp hm x hx nu heig).2

theorem compression_formation_domain (P : Matrix ι ι ℝ) (E : Matrix ι κ ℝ)
    (hP : Pᵀ = P) (hPP : P*P = P) (hE : Eᵀ*E = 1)
    (hp : Function.Injective (P*E).mulVec)
    (hm : Function.Injective ((1-P)*E).mulVec) :
    0 < (compression P E).det ∧ 0 < (1-compression P E).det ∧
      |Offset.asymmetry (compression P E).det (1-compression P E).det| < 1 := by
  have hh := compression_strict P E hP hPP hE hp hm
  have hd := formation_determinants_positive _ hh.1 hh.2
  exact ⟨hd.1, hd.2, Offset.asymmetry_abs_lt hd.1 hd.2⟩

end OperatorFirst.FiniteCovariance

#print axioms OperatorFirst.FiniteCovariance.compression_gram
#print axioms OperatorFirst.FiniteCovariance.complement_projection
#print axioms OperatorFirst.FiniteCovariance.complement_compression
#print axioms OperatorFirst.FiniteCovariance.compression_posSemidef
#print axioms OperatorFirst.FiniteCovariance.compression_posDef
#print axioms OperatorFirst.FiniteCovariance.compression_strict
#print axioms OperatorFirst.FiniteCovariance.formation_determinants_positive
#print axioms OperatorFirst.FiniteCovariance.eigenvalue_in_unit_interval
#print axioms OperatorFirst.FiniteCovariance.compression_formation_domain
