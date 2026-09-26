import OperatorFirst.OffsetEndpoint
example : (fun v : ℝ => v) (-1) - (fun v : ℝ => v) 1 = 2*OperatorFirst.OffsetEndpoint.oddPart (fun v : ℝ => v) 1 := by norm_num [OperatorFirst.OffsetEndpoint.oddPart]
