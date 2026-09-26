import OperatorFirst.LaurentBoundary
open LaurentPolynomial
example : ((C (2:ℚ) * T 1 * (C 3 * T 1) : LaurentPolynomial ℚ).coeff 2) = -6 := by
  norm_num [← single_eq_C_mul_T, AddMonoidAlgebra.single_mul_single,
    AddMonoidAlgebra.coeff_single]
