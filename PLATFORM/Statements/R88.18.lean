import PLATFORM.Statements.«R88.1»
import Foundations.Tensors.PairUnitExponents
import Foundations.Tensors.Semicontinuity.ZariskiSublevel
import Lib.OM.PolMul.Defs

/-- The assembly, case ω = 2, for every level `B > 0`: if every spectral point with sorted
pair exponents of sum at most `2` and `v₀ - 2/3 ≤ 4/3 - B` has `F(1,1,1) ≤ B`, then, if the
exponent of matrix multiplication over `ℂ` is `2`, `asympRank T ≤ n^B` for every `n ≥ 1` (tail
`θ₁ + θ₂ ≤ 4/3 - r`). Applying this lemma at `B = 309/250` under `ω = 2` requires the
stated spectral estimate at that exponent. -/
def S_R88_18 : Prop :=
  ∀ B : ℝ, 0 < B →
  (∀ φ : OM.PolMul.Spectral ℂ, Foundations.PairUnitExponents.theta φ 1 ≤ Foundations.PairUnitExponents.theta φ 0 → Foundations.PairUnitExponents.theta φ 2 ≤ Foundations.PairUnitExponents.theta φ 1 →
    Foundations.PairUnitExponents.theta φ 0 + Foundations.PairUnitExponents.theta φ 1 + Foundations.PairUnitExponents.theta φ 2 ≤ 2 →
    Foundations.PairUnitExponents.theta φ 0 - 2 / 3 ≤ 4 / 3 - B →
    P2M.R88.Fv φ (fun _ => 1) ≤ B) →
  OM.PolMul.omegaF ℂ = 2 →
  ∀ (n : ℕ+) (T : Semicontinuity.KTensor ℂ (fun _ : Fin 3 => n)),
    Semicontinuity.asympRank T ≤ ((n : ℕ) : ℝ) ^ B
