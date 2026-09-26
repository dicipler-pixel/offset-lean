import OperatorFirst.RiceMeleOddSymmetry

/- Deliberately false: the B-sublattice sign is -1. -/
example :
    OperatorFirst.RiceMeleOddSymmetry.bSign (R := ℤ)
      (Sum.inr (0 : Fin 1) : OperatorFirst.RiceMeleOddSymmetry.Site 1) = 1 := by
  norm_num [OperatorFirst.RiceMeleOddSymmetry.bSign]
