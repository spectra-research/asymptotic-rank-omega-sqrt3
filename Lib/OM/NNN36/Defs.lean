import Lib.OM.PolMul.Defs
import Foundations.Tensors.Semicontinuity.ZariskiSublevel
import Mathlib.Analysis.Complex.Basic

namespace OM.NNN36

/-- Supremal asymptotic rank in a fixed three-leg format. -/
noncomputable def formatRankSup (n₁ n₂ n₃ : ℕ+) : ℝ :=
  sSup (Set.range fun T : Semicontinuity.KTensor ℂ (PolMul.fmt n₁ n₂ n₃) =>
    Semicontinuity.asympRank T)

/-- Third vertex on scaling the longest side of the log-dimension triangle to one. -/
noncomputable def normalizedApex (a b c : ℝ) : ℂ :=
  let ξ := (b^2 + c^2 - a^2) / (2*c^2)
  ⟨ξ, Real.sqrt ((b/c)^2 - ξ^2)⟩

end OM.NNN36
