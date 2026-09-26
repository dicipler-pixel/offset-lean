import OperatorFirst.EndpointTransfer
example : OperatorFirst.Offset.asymmetry
    (OperatorFirst.EndpointTransfer.mix (1/2) 1 3)
    (OperatorFirst.EndpointTransfer.mix (-(1/2)) 1 3) = -(1/4 : ℝ) := by
  norm_num [OperatorFirst.Offset.asymmetry, OperatorFirst.EndpointTransfer.mix]
