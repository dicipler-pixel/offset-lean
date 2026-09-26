import OperatorFirst.EndpointProgress

/-! The polynomial band equation, before the Fourier/measure-theoretic step.
E can be either signed band energy: only its squared dispersion enters.
The functions U,W are the polynomial components of a finite-block vector. -/
noncomputable section
open Polynomial
namespace OperatorFirst.BandObstruction

def dispersion (a b A : ℂ) : Polynomial ℂ := C (a*b)*X^2+C A*X+C (a*b)
def numerator (a b v : ℂ) (U W : Polynomial ℂ) : Polynomial ℂ :=
  C v*X*U-(C a*X+C b)*W

/-- Multiplying the first band equation by z clears the Laurent denominator.
This identity uses only the dispersion and that equation on an infinite set. -/
theorem squared_band_identity (a b A v : ℂ) (U W : Polynomial ℂ)
    (E : ℂ → ℂ) (S : Set ℂ) (hS : S.Infinite)
    (hdisp : ∀ z ∈ S, z*(E z)^2 = (dispersion a b A).eval z)
    (hband : ∀ z ∈ S, z*E z*U.eval z = v*z*U.eval z-(a*z+b)*W.eval z) :
    dispersion a b A*(X*U)^2 = X*(numerator a b v U W)^2 := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply hS.mono
  intro z hz
  simp only [Set.mem_setOf_eq, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  rw [← hdisp z hz]
  have hr : (numerator a b v U W).eval z = z*E z*U.eval z := by
    simpa only [numerator, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X] using (hband z hz).symm
  rw [hr]
  ring

/-- No nonzero polynomial spinor can satisfy even the first exact band equation
on an infinite set when both hoppings are nonzero. No positivity hypothesis,
integral identity, or endpoint limit is assumed. -/
theorem polynomial_band_vector_zero (a b A v : ℂ) (hab : a*b ≠ 0)
    (U W : Polynomial ℂ) (E : ℂ → ℂ) (S : Set ℂ) (hS : S.Infinite)
    (hdisp : ∀ z ∈ S, z*(E z)^2 = (dispersion a b A).eval z)
    (hband : ∀ z ∈ S, z*E z*U.eval z = v*z*U.eval z-(a*z+b)*W.eval z) :
    U = 0 ∧ W = 0 := by
  have hU : U = 0 := by
    by_contra hU
    exact EndpointProgress.dispersion_square_obstruction a b A hab (X*U)
      (numerator a b v U W) (mul_ne_zero Polynomial.X_ne_zero hU)
      (squared_band_identity a b A v U W E S hS hdisp hband)
  have hprod : (C a*X+C b)*W = 0 := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply hS.mono
    intro z hz
    simp only [Set.mem_setOf_eq, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_zero]
    have h := hband z hz
    simp only [hU, Polynomial.eval_zero, mul_zero, zero_sub] at h
    linear_combination h
  have hf : C a*X+C b ≠ (0 : Polynomial ℂ) := by
    intro h
    have hc := congrArg (fun q : Polynomial ℂ => q.coeff 0) h
    have hb : b ≠ 0 := (mul_ne_zero_iff.mp hab).2
    apply hb
    simpa using hc
  exact ⟨hU, (mul_eq_zero.mp hprod).resolve_left hf⟩

end OperatorFirst.BandObstruction

#print axioms OperatorFirst.BandObstruction.squared_band_identity
#print axioms OperatorFirst.BandObstruction.polynomial_band_vector_zero
