import OperatorFirst.Offset

/-! Finite algebra for the endpoint reformulation, with explicit limits of scope.
No infinite-chain Fourier integral, covariance strictness theorem, Rice-Mele
endpoint limit, uniform convergence, or physical calibration is assumed here. -/
noncomputable section
open Matrix Filter
open scoped Topology
namespace OperatorFirst.OffsetEndpoint

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℂ
def sigma : Mat2 := !![1,0;0,-1]
def bloch (x y v : ℂ) : Mat2 := !![v,x-y*Complex.I;x+y*Complex.I,-v]
/-- Algebraic formula for the supplied two-band symbol; its spectral and
infinite-chain identifications are separate from the reflection identity. -/
def band (x y v E : ℂ) : Mat2 := (1/2 : ℂ) • (1-E⁻¹ • bloch x y v)

theorem sigma_involution : sigma*sigma=1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sigma,Matrix.mul_apply,Fin.sum_univ_two,Matrix.one_apply]

theorem sublattice_conjugation (x y v : ℂ) :
    sigma*bloch x y v*sigma = -bloch x y (-v) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigma,bloch,Matrix.mul_apply,Fin.sum_univ_two] <;> ring

theorem band_complement_conjugation (x y v E : ℂ) :
    band x y (-v) E = sigma*(1-band x y v E)*sigma := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [band,sigma,bloch,Matrix.mul_apply,Matrix.vecMul,dotProduct,
      Fin.sum_univ_two,Matrix.one_apply,Matrix.sub_apply,Matrix.smul_apply] <;> ring

section Matrices
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem diagonal_conjugation_apply (s : ι → ℂ) (C : Matrix ι ι ℂ) (i j : ι) :
    (diagonal s*C*diagonal s) i j = s i*C i j*s j := by
  simp [Matrix.mul_apply,Matrix.diagonal]

theorem block_complement_conjugation (Cp Cm : Matrix ι ι ℂ) (s : ι → ℂ)
    (f : κ → ι) (hf : Function.Injective f)
    (h : Cm=diagonal s*(1-Cp)*diagonal s) :
    Cm.submatrix f f = diagonal (s ∘ f)*(1-Cp.submatrix f f)*diagonal (s ∘ f) := by
  ext i j
  change Cm (f i) (f j) = _
  rw [h,diagonal_conjugation_apply,diagonal_conjugation_apply]
  simp [Matrix.sub_apply,Matrix.one_apply,hf.eq_iff]

theorem det_involution_sq (S : Matrix ι ι ℂ) (h : S*S=1) : S.det*S.det=1 := by
  have hd := congrArg Matrix.det h
  simpa only [Matrix.det_mul,Matrix.det_one] using hd

theorem complement_determinant_reflection (Cp Cm S : Matrix ι ι ℂ)
    (hS : S*S=1) (h : Cm=S*(1-Cp)*S) : Cm.det=(1-Cp).det := by
  rw [h,Matrix.det_mul,Matrix.det_mul]
  have hs := det_involution_sq S hS
  calc
    S.det*(1-Cp).det*S.det = (S.det*S.det)*(1-Cp).det := by ring
    _ = (1-Cp).det := by rw [hs,one_mul]

theorem determinant_offset_reflection (Cp Cm S : Matrix ι ι ℂ)
    (hS : S*S=1) (h : Cm=S*(1-Cp)*S) :
    Offset.detLogOdds Cp = Real.log ‖Cm.det‖-Real.log ‖Cp.det‖ := by
  rw [complement_determinant_reflection Cp Cm S hS h]
  rfl
end Matrices

def oddPart (F : ℝ → ℝ) (v : ℝ) : ℝ := (F v-F (-v))/2
def evenPart (F : ℝ → ℝ) (v : ℝ) : ℝ := (F v+F (-v))/2

theorem offset_is_negative_twice_odd (F : ℝ → ℝ) (v : ℝ) :
    F (-v)-F v = -2*oddPart F v := by unfold oddPart; ring

theorem even_part_cancels (F : ℝ → ℝ) (v : ℝ) :
    evenPart F (-v)-evenPart F v=0 := by simp [evenPart]; ring

theorem offset_is_odd (F : ℝ → ℝ) (v : ℝ) :
    F (-(-v))-F (-v) = -(F (-v)-F v) := by simp

theorem rate_difference_is_offset_difference (fp₁ fm₁ fp₂ fm₂ : ℝ) :
    ((fp₂-fp₁)-(fm₂-fm₁))/2 = -((fm₂-fp₂)-(fm₁-fp₁))/2 := by ring

theorem equal_rates_iff_equal_offsets (fp₁ fm₁ fp₂ fm₂ : ℝ) :
    fp₂-fp₁=fm₂-fm₁ ↔ fm₂-fp₂=fm₁-fp₁ := by constructor <;> intro h <;> linarith

theorem band_product_excess (a b v : ℝ) :
    ((a-b)^2+v^2)*((a+b)^2+v^2)-v^4 = (a^2-b^2)^2+2*v^2*(a^2+b^2) := by ring

/-- Both positive band-edge squares are needed at v=0. -/
theorem band_product_strict (a b v : ℝ) (hb : 0<b)
    (hminus : 0<(a-b)^2+v^2) (hplus : 0<(a+b)^2+v^2) :
    v^4 < ((a-b)^2+v^2)*((a+b)^2+v^2) := by
  by_cases hv : v=0
  · subst v
    simpa using mul_pos hminus hplus
  · have hv2 : 0<v^2 := sq_pos_of_ne_zero hv
    have hb2 : 0<b^2 := sq_pos_of_pos hb
    have hp := mul_pos hv2 hb2
    have ha := mul_nonneg (le_of_lt hv2) (sq_nonneg a)
    have hi := band_product_excess a b v
    nlinarith [sq_nonneg (a^2-b^2)]

theorem critical_counterexample :
    (((1-1 : ℝ)^2+0^2)*((1+1)^2+0^2))=0^4 := by norm_num

theorem gamma_lt_one (a b v emin emax : ℝ) (hb : 0<b)
    (hemin : 0<emin) (hemax : 0<emax)
    (hmin : emin^2=(a-b)^2+v^2) (hmax : emax^2=(a+b)^2+v^2) :
    |v/Real.sqrt (emin*emax)|<1 := by
  have hm : 0<(a-b)^2+v^2 := by rw [← hmin]; positivity
  have hx : 0<(a+b)^2+v^2 := by rw [← hmax]; positivity
  have hs := band_product_strict a b v hb hm hx
  rw [← hmin,← hmax] at hs
  have hp : 0<emin*emax := mul_pos hemin hemax
  have hg : v^2<emin*emax := by
    by_contra h
    have h1 : 0≤v^2-emin*emax := by linarith
    have h2 : 0≤v^2+emin*emax := by positivity
    have hh := mul_nonneg h1 h2
    nlinarith
  have hq : 0<Real.sqrt (emin*emax) := Real.sqrt_pos.2 hp
  have hq2 := Real.sq_sqrt (le_of_lt hp)
  have hav : |v|<Real.sqrt (emin*emax) := by
    have ha := sq_abs v
    nlinarith [abs_nonneg v,sq_nonneg (|v|-Real.sqrt (emin*emax))]
  rw [abs_div,abs_of_pos hq]
  exact (div_lt_one hq).2 hav

theorem tanh_half_exp (T : ℝ) :
    Real.tanh (T/2) = (Real.exp T-1)/(Real.exp T+1) := by
  rw [Real.tanh_eq,Real.exp_neg]
  have he : Real.exp T = (Real.exp (T/2))^2 := by
    rw [pow_two,← Real.exp_add]
    congr 1 <;> ring
  rw [he]
  have h0 : Real.exp (T/2) ≠ 0 := ne_of_gt (Real.exp_pos _)
  have h1 : Real.exp (T/2)+(Real.exp (T/2))⁻¹ ≠ 0 := by positivity
  have h2 : (Real.exp (T/2))^2+1 ≠ 0 := by positivity
  field_simp [h0,h1,h2] <;> ring

theorem exp_scalarOffset (p m : ℝ) (hp : 0 < p) (hm : 0 < m) :
    Real.exp (Offset.scalarOffset p m)=m/p := by
  rw [Offset.scalarOffset,Real.exp_sub,Real.exp_log hm,Real.exp_log hp]

theorem asymmetry_eq_tanh (p m : ℝ) (hp : 0 < p) (hm : 0 < m) :
    Offset.asymmetry p m = Real.tanh (Offset.scalarOffset p m/2) := by
  rw [tanh_half_exp,exp_scalarOffset p m hp hm]
  unfold Offset.asymmetry
  have hsum : m+p ≠ 0 := ne_of_gt (add_pos hm hp)
  have hratio : m/p+1 ≠ 0 := by positivity
  field_simp [ne_of_gt hp,hsum,hratio] <;> ring

theorem shear_det_one (gamma : ℝ) : (Offset.shear gamma).det=1 := by
  norm_num [Offset.shear,Matrix.det_fin_two]

theorem shear_det_one_and_mixes (gamma : ℝ) (hg : gamma≠0) :
    (Offset.shear gamma).det=1 ∧
    (Offset.shear gamma).mulVec ![1,1] ≠ (1-gamma) • ![1,1] :=
  ⟨shear_det_one gamma,Offset.plus_parity_not_eigenvector hg⟩

def logisticFull (T : ℝ) : ℝ := 1/(1+Real.exp T)
def logisticEmpty (T : ℝ) : ℝ := Real.exp T/(1+Real.exp T)

theorem logistic_probabilities (T : ℝ) :
    0<logisticFull T ∧ 0<logisticEmpty T ∧ logisticFull T+logisticEmpty T=1 := by
  have h : 0<Real.exp T := Real.exp_pos T
  have hd : 1+Real.exp T ≠ 0 := by positivity
  refine ⟨by unfold logisticFull; positivity,by unfold logisticEmpty; positivity,?_⟩
  unfold logisticFull logisticEmpty
  field_simp [hd] <;> ring

theorem logistic_reflection (T : ℝ) : logisticFull (-T)=logisticEmpty T := by
  unfold logisticFull logisticEmpty
  rw [Real.exp_neg]
  have h : Real.exp T ≠ 0 := ne_of_gt (Real.exp_pos T)
  have hp : 1+Real.exp T ≠ 0 := by positivity
  have hi : 1+(Real.exp T)⁻¹ ≠ 0 := by positivity
  field_simp [h,hp,hi] <;> ring

theorem logistic_offset (T : ℝ) :
    Offset.scalarOffset (logisticFull T) (logisticEmpty T)=T := by
  have hd : 1+Real.exp T ≠ 0 := by positivity
  unfold Offset.scalarOffset logisticFull logisticEmpty
  rw [Real.log_div (ne_of_gt (Real.exp_pos T)) hd,
      Real.log_div (by norm_num : (1:ℝ)≠0) hd,Real.log_exp,Real.log_one]
  ring

theorem reflection_allows_linear_growth (n : ℕ) (v : ℝ) :
    Offset.scalarOffset (logisticFull ((n:ℝ)*v)) (logisticFull (-((n:ℝ)*v)))=(n:ℝ)*v := by
  rw [logistic_reflection,logistic_offset]

/-- A finite initial drop followed by a constant tail refutes item 9 exactly. -/
def nonmonotoneExample (n : ℕ) : ℝ := if n=1 then 1/4 else if n=2 then 1/8 else 1/2

theorem nonmonotone_bounded (n : ℕ) :
    0<nonmonotoneExample n ∧ nonmonotoneExample n≤1/2 := by
  unfold nonmonotoneExample
  split_ifs <;> norm_num

theorem nonmonotone_tends : Tendsto nonmonotoneExample atTop (nhds (1/2)) := by
  have he : ∀ᶠ n : ℕ in atTop, nonmonotoneExample n=1/2 := by
    apply Filter.eventually_atTop.2
    refine ⟨3,?_⟩
    intro n hn
    have h1 : n≠1 := by omega
    have h2 : n≠2 := by omega
    simp [nonmonotoneExample,h1,h2]
  exact (Filter.tendsto_congr' he).2 tendsto_const_nhds

theorem nonmonotone_not_monotone : ¬ Monotone nonmonotoneExample := by
  intro h
  have hh := h (show (1:ℕ)≤2 by omega)
  norm_num [nonmonotoneExample] at hh

theorem bounded_convergence_not_monotonicity :
    ¬ (∀ a : ℕ → ℝ, (∀ n, |a n|≤1/2) → Tendsto a atTop (nhds (1/2)) → Monotone a) := by
  intro h
  apply nonmonotone_not_monotone
  apply h nonmonotoneExample
  · intro n
    rw [abs_of_nonneg (le_of_lt (nonmonotone_bounded n).1)]
    exact (nonmonotone_bounded n).2
  · exact nonmonotone_tends

end OperatorFirst.OffsetEndpoint

#print axioms OperatorFirst.OffsetEndpoint.sigma_involution
#print axioms OperatorFirst.OffsetEndpoint.sublattice_conjugation
#print axioms OperatorFirst.OffsetEndpoint.band_complement_conjugation
#print axioms OperatorFirst.OffsetEndpoint.diagonal_conjugation_apply
#print axioms OperatorFirst.OffsetEndpoint.block_complement_conjugation
#print axioms OperatorFirst.OffsetEndpoint.det_involution_sq
#print axioms OperatorFirst.OffsetEndpoint.complement_determinant_reflection
#print axioms OperatorFirst.OffsetEndpoint.determinant_offset_reflection
#print axioms OperatorFirst.OffsetEndpoint.offset_is_negative_twice_odd
#print axioms OperatorFirst.OffsetEndpoint.even_part_cancels
#print axioms OperatorFirst.OffsetEndpoint.offset_is_odd
#print axioms OperatorFirst.OffsetEndpoint.rate_difference_is_offset_difference
#print axioms OperatorFirst.OffsetEndpoint.equal_rates_iff_equal_offsets
#print axioms OperatorFirst.OffsetEndpoint.band_product_excess
#print axioms OperatorFirst.OffsetEndpoint.band_product_strict
#print axioms OperatorFirst.OffsetEndpoint.critical_counterexample
#print axioms OperatorFirst.OffsetEndpoint.gamma_lt_one
#print axioms OperatorFirst.OffsetEndpoint.tanh_half_exp
#print axioms OperatorFirst.OffsetEndpoint.exp_scalarOffset
#print axioms OperatorFirst.OffsetEndpoint.asymmetry_eq_tanh
#print axioms OperatorFirst.OffsetEndpoint.shear_det_one
#print axioms OperatorFirst.OffsetEndpoint.shear_det_one_and_mixes
#print axioms OperatorFirst.OffsetEndpoint.logistic_probabilities
#print axioms OperatorFirst.OffsetEndpoint.logistic_reflection
#print axioms OperatorFirst.OffsetEndpoint.logistic_offset
#print axioms OperatorFirst.OffsetEndpoint.reflection_allows_linear_growth
#print axioms OperatorFirst.OffsetEndpoint.nonmonotone_bounded
#print axioms OperatorFirst.OffsetEndpoint.nonmonotone_tends
#print axioms OperatorFirst.OffsetEndpoint.nonmonotone_not_monotone
#print axioms OperatorFirst.OffsetEndpoint.bounded_convergence_not_monotonicity
