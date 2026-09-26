import OperatorFirst.LaurentBoundary
open LaurentPolynomial
example : ((T 1 * T 1 : LaurentPolynomial ℚ).coeff 2) = 0 := by
  norm_num [← T_add, T_apply]
