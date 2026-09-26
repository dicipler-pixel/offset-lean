import OperatorFirst.EndpointTransfer
example : |OperatorFirst.Offset.asymmetry (1-(1/2)) (1+(1/2)) -
    OperatorFirst.Offset.asymmetry 1 1| ≤ (1/2 : ℝ)/(1+1/2) := by
  norm_num [OperatorFirst.Offset.asymmetry]
