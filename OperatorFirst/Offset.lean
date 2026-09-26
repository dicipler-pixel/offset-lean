import Mathlib

/-!
# The Offset Belongs to the Boundary: finite proof core
Jeromie Beasley's v25, revised formalization 5 September 2026.

Verification is tied to the exact CI commit, not this comment. Physical
occupations are in (0,1). No asymptotic Rice-Mele limit, energy calibration,
spacetime metric, or cosmological constant is assumed or derived here.

The covariance conjugacy, invertibility, and limit hypotheses remain explicit.
This module ports the earlier uncompiled OFFSET-LEAN-V25-01 candidates and
adds finite product log-odds. The physical Gaussian-state interpretation of
those products is separate from their algebraic equality.
-/

noncomputable section
open Matrix Filter
open scoped Topology
namespace OperatorFirst.Offset

structure Occupation where
  nu : ℝ
  positive : 0 < nu
  below_one : nu < 1

def Occupation.flip (c : Occupation) : Occupation where
  nu := 1 - c.nu
  positive := sub_pos.mpr c.below_one
  below_one := by linarith [c.positive]

def Occupation.energy (c : Occupation) : ℝ :=
  Real.log (1 - c.nu) - Real.log c.nu

theorem energy_eq_log_odds (c : Occupation) :
    c.energy = Real.log ((1 - c.nu) / c.nu) := by
  exact (Real.log_div (ne_of_gt (sub_pos.mpr c.below_one))
    (ne_of_gt c.positive)).symm

theorem energy_flip (c : Occupation) : c.flip.energy = -c.energy := by
  change Real.log (1 - (1 - c.nu)) - Real.log (1 - c.nu) =
    -(Real.log (1 - c.nu) - Real.log c.nu)
  rw [show 1 - (1 - c.nu) = c.nu by ring]
  ring

def spectrumOffset (l : List Occupation) : ℝ :=
  (l.map Occupation.energy).sum

theorem spectrumOffset_flip (l : List Occupation) :
    spectrumOffset (l.map Occupation.flip) = -spectrumOffset l := by
  induction l with
  | nil => simp [spectrumOffset]
  | cons c l ih =>
    change c.flip.energy + spectrumOffset (l.map Occupation.flip) =
      -(c.energy + spectrumOffset l)
    rw [energy_flip, ih]
    ring

/-- Spectral pairing implies zero; constructing the pairing is a separate task. -/
theorem protected_zero_of_pairing (l : List Occupation)
    (hpair : l.Perm (l.map Occupation.flip)) : spectrumOffset l = 0 := by
  have hsum := (hpair.map Occupation.energy).sum_eq
  change spectrumOffset l = spectrumOffset (l.map Occupation.flip) at hsum
  rw [spectrumOffset_flip] at hsum
  linarith

theorem exp_energy (c : Occupation) :
    Real.exp c.energy = (1 - c.nu) / c.nu := by
  rw [energy_eq_log_odds]
  exact Real.exp_log (div_pos (sub_pos.mpr c.below_one) c.positive)

/-- For Lambda=2C-I this is the MINUS sign, in exponential coordinates. -/
theorem lambda_energy_dictionary (c : Occupation) :
    2 * c.nu - 1 =
      -((Real.exp c.energy - 1) / (Real.exp c.energy + 1)) := by
  rw [exp_energy]
  have hnu : c.nu ≠ 0 := ne_of_gt c.positive
  have hp : 0 < (1 - c.nu) / c.nu :=
    div_pos (sub_pos.mpr c.below_one) c.positive
  have hden : (1 - c.nu) / c.nu + 1 ≠ 0 := by linarith
  field_simp [hnu, hden] <;> ring

def emptyProbability : List Occupation → ℝ
  | [] => 1
  | c :: l => (1 - c.nu) * emptyProbability l

def fullProbability : List Occupation → ℝ
  | [] => 1
  | c :: l => c.nu * fullProbability l

theorem emptyProbability_positive (l : List Occupation) :
    0 < emptyProbability l := by
  induction l with
  | nil => norm_num [emptyProbability]
  | cons c l ih => exact mul_pos (sub_pos.mpr c.below_one) ih

theorem fullProbability_positive (l : List Occupation) :
    0 < fullProbability l := by
  induction l with
  | nil => norm_num [fullProbability]
  | cons c l ih => exact mul_pos c.positive ih

/-- The finite independent-mode product identity underlying Eq. (15). -/
theorem finite_log_odds (l : List Occupation) :
    spectrumOffset l =
      Real.log (emptyProbability l) - Real.log (fullProbability l) := by
  induction l with
  | nil => simp [spectrumOffset, emptyProbability, fullProbability]
  | cons c l ih =>
    change c.energy + spectrumOffset l =
      Real.log ((1 - c.nu) * emptyProbability l) -
        Real.log (c.nu * fullProbability l)
    rw [Real.log_mul (ne_of_gt (sub_pos.mpr c.below_one))
        (ne_of_gt (emptyProbability_positive l)),
      Real.log_mul (ne_of_gt c.positive) (ne_of_gt (fullProbability_positive l)), ih]
    unfold Occupation.energy
    ring

def asymmetry (p m : ℝ) : ℝ := (m - p) / (m + p)
def commonScale (p m : ℝ) : ℝ := (m + p) / 2
def scalarOffset (p m : ℝ) : ℝ := Real.log m - Real.log p
/-- On (-1,1), this is 2 artanh(a). -/
def logRatio (a : ℝ) : ℝ := Real.log (1 + a) - Real.log (1 - a)

theorem asymmetry_swap (p m : ℝ) :
    asymmetry m p = -asymmetry p m := by
  unfold asymmetry
  rw [add_comm p m]
  rw [show p - m = -(m - p) by ring, neg_div]

theorem commonScale_swap (p m : ℝ) :
    commonScale m p = commonScale p m := by
  unfold commonScale
  ring

theorem commonScale_positive {p m : ℝ} (hp : 0 < p) (hm : 0 < m) :
    0 < commonScale p m := by
  unfold commonScale
  positivity

theorem asymmetry_bounds {p m : ℝ} (hp : 0 < p) (hm : 0 < m) :
    -1 < asymmetry p m ∧ asymmetry p m < 1 := by
  have hd : 0 < m + p := add_pos hm hp
  constructor
  · apply (lt_div_iff₀ hd).2
    linarith
  · apply (div_lt_iff₀ hd).2
    linarith

theorem asymmetry_abs_lt {p m : ℝ} (hp : 0 < p) (hm : 0 < m) :
    |asymmetry p m| < 1 := abs_lt.mpr (asymmetry_bounds hp hm)

theorem common_factor_exact {p m : ℝ} (hp : 0 < p) (hm : 0 < m) :
    commonScale p m * (1 - asymmetry p m) = p ∧
      commonScale p m * (1 + asymmetry p m) = m := by
  have hd : m + p ≠ 0 := ne_of_gt (add_pos hm hp)
  constructor <;> unfold commonScale asymmetry <;> field_simp [hd] <;> ring

theorem endpoint_ratio {p m : ℝ} (hp : 0 < p) (hm : 0 < m) :
    (1 + asymmetry p m) / (1 - asymmetry p m) = m / p := by
  have hd : m + p ≠ 0 := ne_of_gt (add_pos hm hp)
  have ha : 1 - asymmetry p m ≠ 0 := by
    have := (asymmetry_bounds hp hm).2
    linarith
  unfold asymmetry at *
  field_simp [hd, ne_of_gt hp, ha] <;> ring

theorem scalarOffset_eq_logRatio {p m : ℝ} (hp : 0 < p) (hm : 0 < m) :
    scalarOffset p m = logRatio (asymmetry p m) := by
  have hb := asymmetry_bounds hp hm
  have hmA : 1 - asymmetry p m ≠ 0 := by linarith [hb.2]
  have hpA : 1 + asymmetry p m ≠ 0 := by linarith [hb.1]
  unfold scalarOffset logRatio
  rw [← Real.log_div (ne_of_gt hm) (ne_of_gt hp),
    ← Real.log_div hpA hmA, endpoint_ratio hp hm]

theorem logRatio_neg (a : ℝ) : logRatio (-a) = -logRatio a := by
  unfold logRatio
  rw [show 1 + -a = 1 - a by ring, show 1 - -a = 1 + a by ring]
  ring

theorem logRatio_nonnegative {a : ℝ} (ha : 0 ≤ a) (hb : a < 1) :
    0 ≤ logRatio a := by
  unfold logRatio
  apply sub_nonneg.mpr
  apply Real.log_le_log (by linarith)
  linarith

theorem abs_logRatio {a : ℝ} (ha : |a| < 1) :
    |logRatio a| = logRatio |a| := by
  by_cases h : 0 ≤ a
  · rw [abs_of_nonneg h, abs_of_nonneg (logRatio_nonnegative h (abs_lt.mp ha).2)]
  · have hn : 0 ≤ -a := by linarith
    have hlt : -a < 1 := by linarith [(abs_lt.mp ha).1]
    have hf := logRatio_nonnegative hn hlt
    rw [logRatio_neg] at hf
    rw [abs_of_neg (lt_of_not_ge h), abs_of_nonpos (by linarith : logRatio a ≤ 0)]
    exact (logRatio_neg a).symm

theorem abs_scalarOffset {p m : ℝ} (hp : 0 < p) (hm : 0 < m) :
    |scalarOffset p m| = logRatio |asymmetry p m| := by
  rw [scalarOffset_eq_logRatio hp hm]
  exact abs_logRatio (asymmetry_abs_lt hp hm)

theorem cancel_common_determinant {d p m : ℝ}
    (hd : 0 < d) (hp : 0 < p) (hm : 0 < m) :
    Real.log (d * m) - Real.log (d * p) = scalarOffset p m := by
  rw [Real.log_mul (ne_of_gt hd) (ne_of_gt hm),
      Real.log_mul (ne_of_gt hd) (ne_of_gt hp)]
  unfold scalarOffset
  ring

/-- Conditional algebra; NOT a proof that the physical errors have these factors. -/
theorem offset_of_assumed_connection_factors {d gamma p m : ℝ}
    (hd : 0 < d) (hg0 : -1 < gamma) (hg1 : gamma < 1)
    (hp : p = d * (1 - gamma)) (hm : m = d * (1 + gamma)) :
    scalarOffset p m = logRatio gamma := by
  rw [hp, hm]
  exact cancel_common_determinant hd (by linarith) (by linarith)

section Determinants
variable {n k : Type*} [Fintype n] [DecidableEq n]
  [Fintype k] [DecidableEq k]

theorem complement_det_eq_of_conjugacy
    (C S T : Matrix n n ℂ)
    (hST : S * T = 1)
    (hPH : S * C * T = (1 - C).transpose) :
    (1 - C).det = C.det := by
  have hd := congrArg Matrix.det hPH
  have hi := congrArg Matrix.det hST
  simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hd hi
  have hr : S.det * C.det * T.det = (S.det * T.det) * C.det := by ring
  rw [hr, hi, one_mul] at hd
  exact hd.symm

/-- Only for 0<C<I Hermitian is this the physical log-odds. -/
def detLogOdds (C : Matrix n n ℂ) : ℝ :=
  Real.log ‖(1 - C).det‖ - Real.log ‖C.det‖

theorem protected_detLogOdds_zero
    (C S T : Matrix n n ℂ) (hST : S * T = 1)
    (hPH : S * C * T = (1 - C).transpose)
    (_hC : C.det ≠ 0) (_hI : (1 - C).det ≠ 0) :
    detLogOdds C = 0 := by
  unfold detLogOdds
  rw [complement_det_eq_of_conjugacy C S T hST hPH, sub_self]

theorem schur_determinant
    (A : Matrix n n ℂ) (B : Matrix n k ℂ)
    (C : Matrix k n ℂ) (D : Matrix k k ℂ) [Invertible A] :
    (Matrix.fromBlocks A B C D).det =
      A.det * (D - C * ⅟A * B).det := by
  exact Matrix.det_fromBlocks₁₁ A B C D

theorem schur_determinant_ratio
    (A : Matrix n n ℂ) (B : Matrix n k ℂ)
    (C : Matrix k n ℂ) (D : Matrix k k ℂ)
    (A' : Matrix n n ℂ) (B' : Matrix n k ℂ)
    (C' : Matrix k n ℂ) (D' : Matrix k k ℂ)
    [Invertible A] [Invertible A']
    (hdet : A'.det = A.det) (hA : A.det ≠ 0)
    (hS : (D - C * ⅟A * B).det ≠ 0) :
    (Matrix.fromBlocks A' B' C' D').det /
      (Matrix.fromBlocks A B C D).det =
    (D' - C' * ⅟A' * B').det / (D - C * ⅟A * B).det := by
  rw [schur_determinant, schur_determinant, hdet]
  field_simp [hA, hS] <;> ring

theorem involution_cancels_quadratic
    (S X : Matrix n n ℂ) (r : Matrix k n ℂ) (c : Matrix n k ℂ)
    (hS : S * S = 1) :
    ((-r) * S) * (S * X * S) * ((-S) * c) = r * X * c := by
  have hc : S * (S * c) = c := by rw [← Matrix.mul_assoc, hS, Matrix.one_mul]
  have hx : S * (S * (X * c)) = X * c := by
    rw [← Matrix.mul_assoc, hS, Matrix.one_mul]
  calc
    ((-r) * S) * (S * X * S) * ((-S) * c) =
        r * (S * (S * (X * (S * (S * c))))) := by
          simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_assoc]
    _ = r * (S * (S * (X * c))) := by rw [hc]
    _ = r * (X * c) := by rw [hx]
    _ = r * X * c := (Matrix.mul_assoc r X c).symm
end Determinants

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℝ
def shear (gamma : ℝ) : Mat2 := !![1, 0; -2 * gamma, 1]
def parityMatrix (gamma : ℝ) : Mat2 := !![1 - gamma, -gamma; gamma, 1 + gamma]
def parityBasis : Mat2 := !![1, 1; 1, -1]
def parityBasisInv : Mat2 := !![(1/2 : ℝ), 1/2; 1/2, -1/2]

theorem shear_in_parity_coordinates (gamma : ℝ) :
    parityBasisInv * shear gamma * parityBasis = parityMatrix gamma := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [parityBasisInv, parityBasis, shear, parityMatrix,
      Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem shear_characteristic_polynomial (gamma z : ℝ) :
    (z • (1 : Mat2) - shear gamma).det = (z - 1)^2 := by
  simp [shear, Matrix.det_fin_two, Matrix.one_apply] <;> ring

theorem plus_parity_not_eigenvector {gamma : ℝ} (hg : gamma ≠ 0) :
    (shear gamma).mulVec ![1, 1] ≠ (1 - gamma) • ![1, 1] := by
  intro h
  have h0 := congrFun h (0 : Fin 2)
  simp [shear, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0
  apply hg
  linarith

/-- This only preserves an invariant eigenspace algebraically; spectral occupancy
and no-crossing hypotheses are additional when applying it to a ground state. -/
theorem scalar_shift_eigenspace
    {n : Type*} [Fintype n] [DecidableEq n]
    (H P : Matrix n n ℝ) (lambda delta : ℝ)
    (h : H * P = lambda • P) :
    (H + delta • (1 : Matrix n n ℝ)) * P = (lambda + delta) • P := by
  rw [Matrix.add_mul, h, Matrix.smul_mul, Matrix.one_mul, add_smul]

/-- A scalar linear response on a two-dimensional control space has a silent direction. -/
theorem scalar_response_has_silent_direction
    (L : (Fin 2 → ℝ) →ₗ[ℝ] ℝ) :
    ∃ v : Fin 2 → ℝ, v ≠ 0 ∧ L v = 0 := by
  classical
  let e0 : Fin 2 → ℝ := ![1, 0]
  let e1 : Fin 2 → ℝ := ![0, 1]
  by_cases h0 : L e0 = 0
  · refine ⟨e0, ?_, h0⟩
    intro he
    have hc := congrFun he (0 : Fin 2)
    norm_num [e0] at hc
  · let v : Fin 2 → ℝ := (L e1) • e0 - (L e0) • e1
    refine ⟨v, ?_, ?_⟩
    · intro hv
      have hc := congrFun hv (1 : Fin 2)
      have hval : v 1 = -(L e0) := by simp [v, e0, e1]
      rw [hval] at hc
      apply h0
      change -(L e0) = 0 at hc
      linarith
    · change L ((L e1) • e0 - (L e0) • e1) = 0
      rw [map_sub, map_smul, map_smul]
      simp only [smul_eq_mul]
      ring

def counterNu (t : ℝ) : Fin 4 → ℝ :=
  ![1/4 + 27*t, 1/3 - 32*t, 2/3 - 32*t, 3/4 + 27*t]
def counterFull (t : ℝ) : ℝ :=
  (1/4 + 27*t) * (1/3 - 32*t) * (2/3 - 32*t) * (3/4 + 27*t)
def counterEmpty (t : ℝ) : ℝ :=
  (3/4 - 27*t) * (2/3 + 32*t) * (1/3 + 32*t) * (1/4 - 27*t)

theorem counter_occupations_valid (t : ℝ) (ht : |t| < 1/200) :
    ∀ i, 0 < counterNu t i ∧ counterNu t i < 1 := by
  have hlo := (abs_lt.mp ht).1
  have hhi := (abs_lt.mp ht).2
  intro i
  fin_cases i <;> simp [counterNu] <;> constructor <;> linarith

theorem counterFull_expansion (t : ℝ) :
    counterFull t = 746496*t^4 + 4320*t^3 - 510*t^2 + 1/24 := by
  unfold counterFull
  ring

theorem counterEmpty_expansion (t : ℝ) :
    counterEmpty t = 746496*t^4 - 4320*t^3 - 510*t^2 + 1/24 := by
  unfold counterEmpty
  ring

theorem counter_probability_difference (t : ℝ) :
    counterEmpty t - counterFull t = -8640*t^3 := by
  rw [counterFull_expansion, counterEmpty_expansion]
  ring

theorem counter_probability_reflection (t : ℝ) :
    counterEmpty t = counterFull (-t) := by
  rw [counterFull_expansion, counterEmpty_expansion]
  ring

theorem counter_linear_response_vanishes :
    -(27 / ((1/4 : ℝ)*(1-1/4))
      + (-32) / ((1/3 : ℝ)*(1-1/3))
      + (-32) / ((2/3 : ℝ)*(1-2/3))
      + 27 / ((3/4 : ℝ)*(1-3/4))) = 0 := by
  norm_num

theorem census_cutoff_counterexample :
    (2/9 : ℝ) < 1/4 ∧
    (1-(2/9 : ℝ))/(2/9) = 7/2 ∧
    (7/2 : ℝ) < 1/(1/4) ∧
    (7/2 : ℝ) > (1-1/4)/(1/4) := by
  norm_num

theorem occupation_window_iff_odds {nu eps : ℝ}
    (hn0 : 0 < nu) (_hn1 : nu < 1)
    (he0 : 0 < eps) (he1 : eps < 1) :
    (eps ≤ nu ∧ nu ≤ 1-eps) ↔
    (eps/(1-eps) ≤ (1-nu)/nu ∧ (1-nu)/nu ≤ (1-eps)/eps) := by
  have hec : 0 < 1-eps := sub_pos.mpr he1
  rw [div_le_div_iff₀ hec hn0, div_le_div_iff₀ hn0 he0]
  constructor
  · intro h
    constructor <;> nlinarith [h.1, h.2]
  · intro h
    constructor <;> nlinarith [h.1, h.2]

/-- Not a Rice-Mele counterexample: positivity alone cannot fix the coefficient. -/
theorem positive_errors_do_not_fix_gamma :
    (0 : ℝ) < 1/2 ∧ asymmetry (1/2) (1/2) ≠ (1/3 : ℝ) := by
  norm_num [asymmetry]

theorem logRatio_limit {a : ℕ → ℝ} {gamma : ℝ}
    (hg0 : -1 < gamma) (hg1 : gamma < 1)
    (hlim : Tendsto a atTop (𝓝 gamma)) :
    Tendsto (fun n => logRatio (a n)) atTop (𝓝 (logRatio gamma)) := by
  have hp : 1 + gamma ≠ 0 := by linarith
  have hm : 1 - gamma ≠ 0 := by linarith
  exact ((tendsto_const_nhds.add hlim).log hp).sub
    ((tendsto_const_nhds.sub hlim).log hm)

/-- The crucial asymptotic is an explicit premise, never an imported axiom. -/
theorem offset_limit_of_asymmetry_limit
    (p m : ℕ → ℝ) (hp : ∀ n, 0 < p n) (hm : ∀ n, 0 < m n)
    {gamma : ℝ} (hg0 : -1 < gamma) (hg1 : gamma < 1)
    (h_asymmetry_limit :
      Tendsto (fun n => asymmetry (p n) (m n)) atTop (𝓝 gamma)) :
    Tendsto (fun n => scalarOffset (p n) (m n)) atTop
      (𝓝 (logRatio gamma)) := by
  have ht := logRatio_limit hg0 hg1 h_asymmetry_limit
  apply ht.congr'
  exact Filter.Eventually.of_forall fun n =>
    (scalarOffset_eq_logRatio (hp n) (hm n)).symm

/-- Magnitude needs no signed parity assignment, but it still needs its limit. -/
theorem magnitude_limit_of_asymmetry_limit
    (p m : ℕ → ℝ) (hp : ∀ n, 0 < p n) (hm : ∀ n, 0 < m n)
    {gamma : ℝ} (hg0 : 0 ≤ gamma) (hg1 : gamma < 1)
    (h_asymmetry_limit :
      Tendsto (fun n => |asymmetry (p n) (m n)|) atTop (𝓝 gamma)) :
    Tendsto (fun n => |scalarOffset (p n) (m n)|) atTop
      (𝓝 (logRatio gamma)) := by
  have ht := logRatio_limit (by linarith : -1 < gamma) hg1 h_asymmetry_limit
  apply ht.congr'
  exact Filter.Eventually.of_forall fun n =>
    (abs_scalarOffset (hp n) (hm n)).symm

end OperatorFirst.Offset

#print axioms OperatorFirst.Offset.energy_eq_log_odds
#print axioms OperatorFirst.Offset.energy_flip
#print axioms OperatorFirst.Offset.spectrumOffset_flip
#print axioms OperatorFirst.Offset.protected_zero_of_pairing
#print axioms OperatorFirst.Offset.exp_energy
#print axioms OperatorFirst.Offset.lambda_energy_dictionary
#print axioms OperatorFirst.Offset.emptyProbability_positive
#print axioms OperatorFirst.Offset.fullProbability_positive
#print axioms OperatorFirst.Offset.finite_log_odds
#print axioms OperatorFirst.Offset.asymmetry_swap
#print axioms OperatorFirst.Offset.commonScale_swap
#print axioms OperatorFirst.Offset.commonScale_positive
#print axioms OperatorFirst.Offset.asymmetry_bounds
#print axioms OperatorFirst.Offset.asymmetry_abs_lt
#print axioms OperatorFirst.Offset.common_factor_exact
#print axioms OperatorFirst.Offset.endpoint_ratio
#print axioms OperatorFirst.Offset.scalarOffset_eq_logRatio
#print axioms OperatorFirst.Offset.logRatio_neg
#print axioms OperatorFirst.Offset.logRatio_nonnegative
#print axioms OperatorFirst.Offset.abs_logRatio
#print axioms OperatorFirst.Offset.abs_scalarOffset
#print axioms OperatorFirst.Offset.cancel_common_determinant
#print axioms OperatorFirst.Offset.offset_of_assumed_connection_factors
#print axioms OperatorFirst.Offset.complement_det_eq_of_conjugacy
#print axioms OperatorFirst.Offset.protected_detLogOdds_zero
#print axioms OperatorFirst.Offset.schur_determinant
#print axioms OperatorFirst.Offset.schur_determinant_ratio
#print axioms OperatorFirst.Offset.involution_cancels_quadratic
#print axioms OperatorFirst.Offset.shear_in_parity_coordinates
#print axioms OperatorFirst.Offset.shear_characteristic_polynomial
#print axioms OperatorFirst.Offset.plus_parity_not_eigenvector
#print axioms OperatorFirst.Offset.scalar_shift_eigenspace
#print axioms OperatorFirst.Offset.scalar_response_has_silent_direction
#print axioms OperatorFirst.Offset.counter_occupations_valid
#print axioms OperatorFirst.Offset.counterFull_expansion
#print axioms OperatorFirst.Offset.counterEmpty_expansion
#print axioms OperatorFirst.Offset.counter_probability_difference
#print axioms OperatorFirst.Offset.counter_probability_reflection
#print axioms OperatorFirst.Offset.counter_linear_response_vanishes
#print axioms OperatorFirst.Offset.census_cutoff_counterexample
#print axioms OperatorFirst.Offset.occupation_window_iff_odds
#print axioms OperatorFirst.Offset.positive_errors_do_not_fix_gamma
#print axioms OperatorFirst.Offset.logRatio_limit
#print axioms OperatorFirst.Offset.offset_limit_of_asymmetry_limit
#print axioms OperatorFirst.Offset.magnitude_limit_of_asymmetry_limit
