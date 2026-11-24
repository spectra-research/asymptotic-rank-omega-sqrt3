import Lib.OM.PolMul.Defs
import Foundations.Tensors.Semicontinuity.ZariskiSublevel

namespace P2M.R115

noncomputable def formatRankSup (n₁ n₂ n₃ : ℕ+) : ℝ :=
  sSup (Set.range fun T : Semicontinuity.KTensor ℂ (OM.PolMul.fmt n₁ n₂ n₃) =>
    Semicontinuity.asympRank T)

end P2M.R115
