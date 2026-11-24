import PLATFORM.Statements.«R113.7»
import Lib.OM.PolMul.Defs

open OM.PolMul

def S_R116_3 : Prop :=
  P2M.R113.gamma = 1 → ∀ (b₁₂ b₁₃ b₂₃ : ℕ+)
    (T : T3 ℂ (fmt (b₁₂ * b₁₃) (b₁₂ * b₂₃) (b₁₃ * b₂₃))),
    AsympRestricts T (matMul b₁₃ b₁₂ b₂₃)
