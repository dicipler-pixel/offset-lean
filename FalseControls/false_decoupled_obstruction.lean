import OperatorFirst.BandObstruction
example : ¬ ((∀ z : ℂ, z*(1:ℂ)^2 =
    (OperatorFirst.BandObstruction.dispersion 0 0 1).eval z) ∧
    (∀ z : ℂ, z*1*(1:Polynomial ℂ).eval z =
      1*z*(1:Polynomial ℂ).eval z-(0*z+0)*(0:Polynomial ℂ).eval z)) := by
  norm_num [OperatorFirst.BandObstruction.dispersion]
