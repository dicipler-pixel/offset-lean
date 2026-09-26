import OperatorFirst.EndpointProgress

/-! Finite transfer and relative-error calculus for the Offset endpoint.
The all-size Rice–Mele interpolation and the Hankel limit are NOT premises
silently discharged here: applications must supply them explicitly. -/
noncomputable section
open Filter
open scoped Topology
namespace OperatorFirst.EndpointTransfer
open Offset

def mix (t p m : ℝ) : ℝ := (1+t)/2*p + (1-t)/2*m

theorem mix_reflection (t p m : ℝ) : mix (-t) p m = mix t m p := by
  unfold mix
  ring

theorem mix_sum (t p m : ℝ) : mix (-t) p m + mix t p m = m+p := by
  unfold mix
  ring

theorem mix_difference (t p m : ℝ) :
    mix (-t) p m - mix t p m = t*(m-p) := by
  unfold mix
  ring

theorem mix_positive {t p m : ℝ} (ht : |t| ≤ 1)
    (hp : 0 < p) (hm : 0 < m) : 0 < mix t p m := by
  obtain ⟨ht0, ht1⟩ := abs_le.mp ht
  have h0 : 0 ≤ (1+t)/2 := by linarith
  have h1 : 0 ≤ (1-t)/2 := by linarith
  by_cases h : t = -1
  · simp [mix, h, hm]
  · have hlt : -1 < t := lt_of_le_of_ne ht0 (Ne.symm h)
    have hh : 0 < (1+t)/2 := by linarith
    exact add_pos_of_pos_of_nonneg (mul_pos hh hp) (mul_nonneg h1 hm.le)

theorem mix_asymmetry (t p m : ℝ) :
    asymmetry (mix t p m) (mix (-t) p m) = t*asymmetry p m := by
  unfold asymmetry
  rw [mix_difference, mix_sum]
  ring

theorem mass_within_gap {a b v e : ℝ} (he : 0 < e)
    (heq : e^2 = (a-b)^2+v^2) : |v/e| ≤ 1 := by
  have hv : |v| ≤ e := by
    nlinarith [sq_abs v, abs_nonneg v, sq_nonneg (a-b)]
  rw [abs_div, abs_of_pos he]
  exact (div_le_one he).2 hv

/-- The existing affine determinant formula really implies the three-site
interpolation between equal-invariant endpoint matrices. -/
theorem three_site_transfer (a b v t e x y : ℝ) (he : e ≠ 0)
    (hA : a^2+b^2+v^2 = t^2+t^2+e^2) (hp : a*b = t*t) :
    (EndpointProgress.threeSite a b v x y).det =
      mix (v/e) (EndpointProgress.threeSite t t e x y).det
        (EndpointProgress.threeSite t t (-e) x y).det := by
  simp only [EndpointProgress.three_site_affine, neg_sq]
  rw [hA, hp]
  unfold mix
  field_simp [he]
  <;> ring

/-- Conditional application to a supplied all-size determinant transfer. -/
theorem signed_limit_of_exact_transfer
    (p m P Q s : ℕ → ℝ) (t beta : ℝ)
    (hp : ∀ n, p n = mix t (P n) (Q n))
    (hm : ∀ n, m n = mix (-t) (P n) (Q n))
    (hlim : Tendsto (fun n => s n * asymmetry (P n) (Q n)) atTop (nhds beta)) :
    Tendsto (fun n => s n * asymmetry (p n) (m n)) atTop (nhds (t*beta)) := by
  have h := hlim.const_mul t
  convert h using 1
  ext n
  rw [hp n, hm n, mix_asymmetry]
  ring

theorem perturbation_positive {p d eps : ℝ} (hp : 0 < p)
    (heps : eps < 1) (hd : |d| ≤ eps*p) : 0 < p+d := by
  have h := (abs_le.mp hd).1
  have hprod := mul_pos (sub_pos.mpr heps) hp
  nlinarith

theorem perturbation_defect (p m dp dm : ℝ)
    (hs : m+p ≠ 0) (hd : m+dm+(p+dp) ≠ 0) :
    asymmetry (p+dp) (m+dm) - asymmetry p m =
      ((1-asymmetry p m)*dm-(1+asymmetry p m)*dp)/(m+dm+(p+dp)) := by
  unfold asymmetry
  field_simp [hs, hd]
  <;> ring

theorem asymmetry_variance (p m : ℝ) (hs : m+p ≠ 0) :
    (1-asymmetry p m)*m+(1+asymmetry p m)*p =
      (1-(asymmetry p m)^2)*(m+p) := by
  unfold asymmetry
  field_simp [hs]
  <;> ring

/-- The variance factor 1-g² in manuscript E26 is retained. -/
theorem relative_error_bound_with_variance {p m dp dm eps : ℝ}
    (hp : 0 < p) (hm : 0 < m) (he0 : 0 ≤ eps) (he1 : eps < 1)
    (hdp : |dp| ≤ eps*p) (hdm : |dm| ≤ eps*m) :
    |asymmetry (p+dp) (m+dm)-asymmetry p m| ≤
      eps*(1-(asymmetry p m)^2)/(1-eps) := by
  let g := asymmetry p m
  have hg := asymmetry_bounds hp hm
  have hgm : 0 ≤ 1-g := by dsimp [g]; linarith [hg.2]
  have hgp : 0 ≤ 1+g := by dsimp [g]; linarith [hg.1]
  have hs : 0 < m+p := add_pos hm hp
  have he : 0 < 1-eps := sub_pos.mpr he1
  have hvar := asymmetry_variance p m (ne_of_gt hs)
  change (1-g)*m+(1+g)*p = (1-g^2)*(m+p) at hvar
  have hv : 0 ≤ 1-g^2 := by
    have ht := mul_nonneg hgm hgp
    nlinarith
  have hlow : (1-eps)*(m+p) ≤ m+dm+(p+dp) := by
    have h1 := (abs_le.mp hdp).1
    have h2 := (abs_le.mp hdm).1
    nlinarith
  have hb : 0 < (1-eps)*(m+p) := mul_pos he hs
  have hd : 0 < m+dm+(p+dp) := lt_of_lt_of_le hb hlow
  have hn : |(1-g)*dm-(1+g)*dp| ≤ eps*(1-g^2)*(m+p) := by
    calc
      |(1-g)*dm-(1+g)*dp| ≤ |(1-g)*dm|+|(1+g)*dp| := abs_sub _ _
      _ = (1-g)*|dm|+(1+g)*|dp| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hgm, abs_of_nonneg hgp]
      _ ≤ (1-g)*(eps*m)+(1+g)*(eps*p) :=
        add_le_add (mul_le_mul_of_nonneg_left hdm hgm)
          (mul_le_mul_of_nonneg_left hdp hgp)
      _ = eps*((1-g)*m+(1+g)*p) := by ring
      _ = eps*(1-g^2)*(m+p) := by rw [hvar]; ring
  rw [perturbation_defect p m dp dm (ne_of_gt hs) (ne_of_gt hd),
    abs_div, abs_of_pos hd]
  change |(1-g)*dm-(1+g)*dp|/(m+dm+(p+dp)) ≤ eps*(1-g^2)/(1-eps)
  calc
    _ ≤ (eps*(1-g^2)*(m+p))/(m+dm+(p+dp)) :=
      div_le_div_of_nonneg_right hn hd.le
    _ ≤ (eps*(1-g^2)*(m+p))/((1-eps)*(m+p)) :=
      div_le_div_of_nonneg_left (by positivity) hb hlow
    _ = eps*(1-g^2)/(1-eps) := by field_simp <;> ring

theorem relative_error_bound {p m dp dm eps : ℝ}
    (hp : 0 < p) (hm : 0 < m) (he0 : 0 ≤ eps) (he1 : eps < 1)
    (hdp : |dp| ≤ eps*p) (hdm : |dm| ≤ eps*m) :
    |asymmetry (p+dp) (m+dm)-asymmetry p m| ≤ eps/(1-eps) := by
  apply (relative_error_bound_with_variance hp hm he0 he1 hdp hdm).trans
  apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr he1.le)
  nlinarith [mul_nonneg he0 (sq_nonneg (asymmetry p m))]

/-- Vanishing relative determinant errors transfer a supplied asymmetry limit.
This does not assert that the physical errors satisfy the bound. -/
theorem limit_of_relative_errors (p m dp dm eps : ℕ → ℝ) (gamma : ℝ)
    (hp : ∀ n, 0 < p n) (hm : ∀ n, 0 < m n)
    (he0 : ∀ n, 0 ≤ eps n) (he1 : ∀ n, eps n < 1)
    (hdp : ∀ n, |dp n| ≤ eps n*p n) (hdm : ∀ n, |dm n| ≤ eps n*m n)
    (heps : Tendsto eps atTop (nhds 0))
    (hg : Tendsto (fun n => asymmetry (p n) (m n)) atTop (nhds gamma)) :
    Tendsto (fun n => asymmetry (p n+dp n) (m n+dm n)) atTop (nhds gamma) := by
  have hb : Tendsto (fun n => eps n/(1-eps n)) atTop (nhds 0) := by
    convert heps.div (tendsto_const_nhds.sub heps) (by norm_num : (1:ℝ)-0 ≠ 0) using 1
    · ext n
      rfl
    · norm_num
  have ha : Tendsto (fun n => |asymmetry (p n+dp n) (m n+dm n)-asymmetry (p n) (m n)|)
      atTop (nhds 0) :=
    squeeze_zero (fun n => abs_nonneg _) (fun n =>
      relative_error_bound (hp n) (hm n) (he0 n) (he1 n) (hdp n) (hdm n)) hb
  have hz : Tendsto (fun n => asymmetry (p n+dp n) (m n+dm n)-asymmetry (p n) (m n))
      atTop (nhds 0) := by
    exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using ha)
  simpa using hz.add hg

/-- Signed convergence handles a varying parity factor with |s_n|=1. -/
theorem signed_limit_of_relative_errors (p m dp dm eps s : ℕ → ℝ) (gamma : ℝ)
    (hp : ∀ n, 0 < p n) (hm : ∀ n, 0 < m n)
    (he0 : ∀ n, 0 ≤ eps n) (he1 : ∀ n, eps n < 1)
    (hdp : ∀ n, |dp n| ≤ eps n*p n) (hdm : ∀ n, |dm n| ≤ eps n*m n)
    (hs : ∀ n, |s n| = 1) (heps : Tendsto eps atTop (nhds 0))
    (hg : Tendsto (fun n => s n*asymmetry (p n) (m n)) atTop (nhds gamma)) :
    Tendsto (fun n => s n*asymmetry (p n+dp n) (m n+dm n)) atTop (nhds gamma) := by
  have hb : Tendsto (fun n => eps n/(1-eps n)) atTop (nhds 0) := by
    convert heps.div (tendsto_const_nhds.sub heps) (by norm_num : (1:ℝ)-0 ≠ 0) using 1
    · ext n
      rfl
    · norm_num
  have ha : Tendsto (fun n => |s n*asymmetry (p n+dp n) (m n+dm n)-
      s n*asymmetry (p n) (m n)|) atTop (nhds 0) := by
    apply squeeze_zero (fun n => abs_nonneg _) _ hb
    intro n
    rw [← mul_sub, abs_mul, hs n, one_mul]
    exact relative_error_bound (hp n) (hm n) (he0 n) (he1 n) (hdp n) (hdm n)
  have hz : Tendsto (fun n => s n*asymmetry (p n+dp n) (m n+dm n)-
      s n*asymmetry (p n) (m n)) atTop (nhds 0) := by
    exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using ha)
  simpa using hz.add hg

/-- Converts a parity-corrected limit into the physical half-offset magnitude.
The parity need not itself converge. -/
theorem half_offset_magnitude_of_signed_limit (p m s : ℕ → ℝ) (gamma : ℝ)
    (hp : ∀ n, 0 < p n) (hm : ∀ n, 0 < m n)
    (hs : ∀ n, |s n| = 1) (hgamma : |gamma| < 1)
    (hlim : Tendsto (fun n => s n*asymmetry (p n) (m n)) atTop (nhds gamma)) :
    Tendsto (fun n => |scalarOffset (p n) (m n)|/2) atTop
      (nhds (logRatio |gamma|/2)) := by
  have ha : Tendsto (fun n => |asymmetry (p n) (m n)|) atTop (nhds |gamma|) := by
    simpa only [abs_mul, hs, one_mul] using hlim.abs
  exact (magnitude_limit_of_asymmetry_limit p m hp hm (abs_nonneg gamma) hgamma ha).div_const 2

/-- End-to-end conditional approximate transfer, including positivity,
parity, and conversion to the half-offset magnitude. -/
theorem endpoint_of_approximate_transfer (P Q dp dm eps s : ℕ → ℝ) (t beta : ℝ)
    (ht : |t| ≤ 1) (hP : ∀ n, 0 < P n) (hQ : ∀ n, 0 < Q n)
    (he0 : ∀ n, 0 ≤ eps n) (he1 : ∀ n, eps n < 1)
    (hdp : ∀ n, |dp n| ≤ eps n*mix t (P n) (Q n))
    (hdm : ∀ n, |dm n| ≤ eps n*mix (-t) (P n) (Q n))
    (hs : ∀ n, |s n| = 1) (heps : Tendsto eps atTop (nhds 0))
    (hbeta : |t*beta| < 1)
    (hlim : Tendsto (fun n => s n*asymmetry (P n) (Q n)) atTop (nhds beta)) :
    Tendsto (fun n => |scalarOffset (mix t (P n) (Q n)+dp n)
      (mix (-t) (P n) (Q n)+dm n)|/2) atTop (nhds (logRatio |t*beta|/2)) := by
  have hp : ∀ n, 0 < mix t (P n) (Q n) := fun n => mix_positive ht (hP n) (hQ n)
  have hm : ∀ n, 0 < mix (-t) (P n) (Q n) := fun n =>
    mix_positive (by simpa only [abs_neg] using ht) (hP n) (hQ n)
  have hg := signed_limit_of_exact_transfer
    (fun n => mix t (P n) (Q n)) (fun n => mix (-t) (P n) (Q n)) P Q s t beta
    (fun _ => rfl) (fun _ => rfl) hlim
  have ha := signed_limit_of_relative_errors _ _ dp dm eps s (t*beta)
    hp hm he0 he1 hdp hdm hs heps hg
  exact half_offset_magnitude_of_signed_limit _ _ s (t*beta)
    (fun n => perturbation_positive (hp n) (he1 n) (hdp n))
    (fun n => perturbation_positive (hm n) (he1 n) (hdm n)) hs hbeta ha

end OperatorFirst.EndpointTransfer

#print axioms OperatorFirst.EndpointTransfer.mix_reflection
#print axioms OperatorFirst.EndpointTransfer.mix_sum
#print axioms OperatorFirst.EndpointTransfer.mix_difference
#print axioms OperatorFirst.EndpointTransfer.mix_positive
#print axioms OperatorFirst.EndpointTransfer.mix_asymmetry
#print axioms OperatorFirst.EndpointTransfer.mass_within_gap
#print axioms OperatorFirst.EndpointTransfer.three_site_transfer
#print axioms OperatorFirst.EndpointTransfer.signed_limit_of_exact_transfer
#print axioms OperatorFirst.EndpointTransfer.perturbation_positive
#print axioms OperatorFirst.EndpointTransfer.perturbation_defect
#print axioms OperatorFirst.EndpointTransfer.asymmetry_variance
#print axioms OperatorFirst.EndpointTransfer.relative_error_bound_with_variance
#print axioms OperatorFirst.EndpointTransfer.relative_error_bound
#print axioms OperatorFirst.EndpointTransfer.limit_of_relative_errors
#print axioms OperatorFirst.EndpointTransfer.signed_limit_of_relative_errors
#print axioms OperatorFirst.EndpointTransfer.half_offset_magnitude_of_signed_limit
#print axioms OperatorFirst.EndpointTransfer.endpoint_of_approximate_transfer
