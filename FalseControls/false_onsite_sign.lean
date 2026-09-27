import OperatorFirst.BoundaryModel
open OperatorFirst.BoundaryModel
example : (onsite 0).coeff 1 = -Complex.I := by
  rw [onsite_top]
  norm_num [Complex.ext_iff]
