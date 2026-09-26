import OperatorFirst.OffsetEndpoint

/-! New endpoint work. The polynomial obstruction and three-site reduction are
proved here. Infinite-chain positivity is explained analytically in the companion
note, not formalized here. No all-size isospectral identity or endpoint limit is
assumed. -/
noncomputable section
open Matrix Polynomial Filter
open scoped Topology
namespace OperatorFirst.EndpointProgress

def threeSite (a b v x y : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1-v*x, a*x+b*y, -v*y;
     a*x+b*y, 1+v*x, a*y+b*x;
     -v*y, a*y+b*x, 1-v*x]

def evenThree (A p x y : ℝ) := 1-A*(x^2+y^2)-4*p*x*y

def oddThree (A p x y : ℝ) := x-(x^2-y^2)*(A*x+2*p*y)

/-- Exact for arbitrary real Fourier entries x,y, without an endpoint hypothesis.
The matrix is twice the physical three-site covariance when x=g_0,y=g_1. -/
theorem three_site_affine (a b v x y : ℝ) :
    (threeSite a b v x y).det =
      evenThree (a^2+b^2+v^2) (a*b) x y -
        v*oddThree (a^2+b^2+v^2) (a*b) x y := by
  simp [threeSite, Matrix.det_fin_three, evenThree, oddThree]
  <;> ring

theorem three_site_reflected_sum (a b v x y : ℝ) :
    (threeSite a b (-v) x y).det + (threeSite a b v x y).det =
      2*evenThree (a^2+b^2+v^2) (a*b) x y := by
  rw [three_site_affine, three_site_affine]
  simp only [neg_sq]
  ring

theorem three_site_reflected_difference (a b v x y : ℝ) :
    (threeSite a b (-v) x y).det - (threeSite a b v x y).det =
      2*v*oddThree (a^2+b^2+v^2) (a*b) x y := by
  rw [three_site_affine, three_site_affine]
  simp only [neg_sq]
  ring

theorem three_site_asymmetry (a b v x y : ℝ) :
    ((threeSite a b (-v) x y).det - (threeSite a b v x y).det) /
      ((threeSite a b (-v) x y).det + (threeSite a b v x y).det) =
      v * oddThree (a^2+b^2+v^2) (a*b) x y /
        evenThree (a^2+b^2+v^2) (a*b) x y := by
  rw [three_site_reflected_difference, three_site_reflected_sum]
  ring

/-- A polynomial with nonzero constant term cannot turn a nonzero square
into X times a square. This is the algebraic obstruction to a finitely supported
exact band eigenvector, after clearing Laurent powers. -/
theorem odd_valuation_obstruction (P U V : Polynomial ℂ)
    (hP : P.coeff 0 ≠ 0) (hU : U ≠ 0) : P*U^2 ≠ X*V^2 := by
  intro heq
  have hp : P ≠ 0 := by
    intro h
    simp [h] at hP
  have hv : V ≠ 0 := by
    intro h
    have hn : P*U^2 ≠ 0 := mul_ne_zero hp (pow_ne_zero 2 hU)
    apply hn
    simpa [h] using heq
  have hd := congrArg Polynomial.natTrailingDegree heq
  have hzero : P.natTrailingDegree = 0 :=
    Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr hP)
  simp only [pow_two, Polynomial.natTrailingDegree_mul hp (mul_ne_zero hU hU),
    Polynomial.natTrailingDegree_mul hU hU,
    Polynomial.natTrailingDegree_mul Polynomial.X_ne_zero (mul_ne_zero hv hv),
    Polynomial.natTrailingDegree_mul hv hv,
    Polynomial.natTrailingDegree_X, hzero, zero_add] at hd
  omega

/-- The Rice-Mele Laurent dispersion has an odd pole at zero whenever ab ≠ 0. -/
theorem dispersion_square_obstruction (a b A : ℂ) (hab : a*b ≠ 0)
    (U V : Polynomial ℂ) (hU : U ≠ 0) :
    (C (a*b)*X^2+C A*X+C (a*b))*U^2 ≠ X*V^2 := by
  apply odd_valuation_obstruction _ U V _ hU
  simpa using hab

/-- Relative, rather than absolute, determinant errors are the endpoint target. -/
theorem normalized_defect (p m gamma : ℝ) (hs : m+p ≠ 0) :
    (m-p)/(m+p)-gamma = ((1-gamma)*m-(1+gamma)*p)/(m+p) := by
  field_simp
  <;> ring

/-- A signed determinant ratio gives the logarithmic endpoint once its positive
limit is established. This lemma asserts no Rice-Mele convergence. -/
theorem log_ratio_limit (r : ℕ → ℝ) (gamma : ℝ)
    (hg0 : 0 < (1+gamma)/(1-gamma))
    (hr : Tendsto r atTop (nhds ((1+gamma)/(1-gamma)))) :
    Tendsto (fun n => Real.log (r n)/2) atTop
      (nhds (Real.log ((1+gamma)/(1-gamma))/2)) := by
  exact (hr.log (ne_of_gt hg0)).div_const 2

end OperatorFirst.EndpointProgress

#print axioms OperatorFirst.EndpointProgress.three_site_affine
#print axioms OperatorFirst.EndpointProgress.three_site_reflected_sum
#print axioms OperatorFirst.EndpointProgress.three_site_reflected_difference
#print axioms OperatorFirst.EndpointProgress.three_site_asymmetry
#print axioms OperatorFirst.EndpointProgress.odd_valuation_obstruction
#print axioms OperatorFirst.EndpointProgress.dispersion_square_obstruction
#print axioms OperatorFirst.EndpointProgress.normalized_defect
#print axioms OperatorFirst.EndpointProgress.log_ratio_limit
