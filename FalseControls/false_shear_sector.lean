import OperatorFirst.Offset
open Matrix OperatorFirst.Offset
example : (shear (1/3)).mulVec ![1, 1] = (2/3 : Real) • ![1, 1] := by
  ext i
  fin_cases i <;> norm_num [shear, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
