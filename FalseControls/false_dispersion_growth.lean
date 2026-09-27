import OperatorFirst.BoundaryModel
open OperatorFirst.BoundaryModel
example : (mon 1 1 ^ 2 + mon 0 (-1) ^ 2 + onsite 0 ^ 2).coeff 2 = 1 := by
  rw [chart_dispersion]
  norm_num [mon]
