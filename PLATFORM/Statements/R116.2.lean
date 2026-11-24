import Mathlib.Analysis.Real.Sqrt

namespace P2M.R116

noncomputable def discRadius (a b c : ℝ) : ℝ :=
  let s := (a + b + c) / 2
  if c ^ 2 < a ^ 2 + b ^ 2 then
    a * b * c / (4 * Real.sqrt (s * (s - a) * (s - b) * (s - c)))
  else c / 2

end P2M.R116
