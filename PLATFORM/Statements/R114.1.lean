import Foundations.Tensors.Semicontinuity.ZariskiSublevel
import Mathlib.Basic.Complex.Basic

namespace P2M.R114

noncomputable def cubeRankSup (n : ℕ+) : ℝ :=
  sSup (Set.range fun T : Semicontinuity.KTensor ℂ (fun _ : Fin 3 => n) =>
    Semicontinuity.asympRank T)

end P2M.R114
