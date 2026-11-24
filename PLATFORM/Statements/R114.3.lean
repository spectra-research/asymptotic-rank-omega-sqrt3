import Lib.OM.PolMul.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace P2M.R114

noncomputable def relativeCost {D : ℕ+} (T : Semicontinuity.KTensor ℂ (fun _ : Fin 3 => D)) : ℝ := by
  classical
  exact if D < 2 ∨ T = 0 then 0 else
    sSup (Set.range fun φ : OM.PolMul.Spectral ℂ =>
      Real.logb 2 (φ.eval T) /
        (Real.logb 2 ((D : ℕ) : ℝ) * Real.logb 2 (φ.eval (OM.PolMul.matMul 2 2 2))))

end P2M.R114
