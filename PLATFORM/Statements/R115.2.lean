import Mathlib.Analysis.Complex.Basic

namespace P2M.R115

noncomputable def normalizedApex (a b c : ℝ) : ℂ :=
  let ξ := (b ^ 2 + c ^ 2 - a ^ 2) / (2 * c ^ 2)
  ⟨ξ, Real.sqrt ((b / c) ^ 2 - ξ ^ 2)⟩

end P2M.R115
