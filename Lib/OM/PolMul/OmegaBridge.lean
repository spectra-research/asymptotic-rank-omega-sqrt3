/- Adapted from PolMul/OmegaBridge.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMul.OmegaBridge.Growth

namespace OM.PolMul

open AsymptoticSpectrumDuality
open OM.PolMulDef

universe u

variable (F : Type u) [Field F]

/-- Strassen's asymptotic rank of the `2 × 2` matrix-multiplication class is
`2 ^ omegaF F`.  This is the formal bridge between the size-based definition
of `omegaF` and powers in the tensor semiring. -/
theorem two_rpow_omegaF :
    (2 : ℝ) ^ omegaF F =
      (OmegaBridge.pF F).asympRank (OmegaBridge.mmClass F) := by
  rw [OmegaBridge.omegaF_eq_logb_asympRank]
  exact Real.rpow_logb (by norm_num) (by norm_num)
    (zero_lt_one.trans_le (OmegaBridge.one_le_asympRank_mmClass F))

end OM.PolMul
