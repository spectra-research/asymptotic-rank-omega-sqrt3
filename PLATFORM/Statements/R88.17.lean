import PLATFORM.Statements.«R88.1»
import Foundations.Tensors.PairUnitExponents
import Foundations.Tensors.Semicontinuity.ZariskiSublevel

/-- The assembly, unconditional case, for every level `B > 0`: if every spectral point with
sorted pair exponents in the rectangular region and `r = v₀ - mean ≤ 3/2 - B` has `F(1,1,1) ≤ B`,
then `asympRank T ≤ n^B` for every `n ≥ 1` and every complex `n × n × n` tensor (relabelling to
sorted exponents, the rectangular region `R88.8`, the coefficient-star tail `F(1,1,1) ≤ θ₁ + θ₂ ≤
3/2 - r` for `r ≥ 3/2 - B`, tensor powers, dyadic padding and spectrum duality). Applying this
lemma at `B = 2779/2000` requires the stated spectral estimate at that exponent. -/
def S_R88_17 : Prop :=
  ∀ B : ℝ, 0 < B →
  (∀ φ : OM.PolMul.Spectral ℂ, Foundations.PairUnitExponents.theta φ 1 ≤ Foundations.PairUnitExponents.theta φ 0 → Foundations.PairUnitExponents.theta φ 2 ≤ Foundations.PairUnitExponents.theta φ 1 →
    Foundations.PairUnitExponents.theta φ 0 + Foundations.PairUnitExponents.theta φ 1 + Foundations.PairUnitExponents.theta φ 2 ≤
      2 + 2 * Real.sqrt ((1 - Foundations.PairUnitExponents.theta φ 0) * (1 - Foundations.PairUnitExponents.theta φ 1) * (1 - Foundations.PairUnitExponents.theta φ 2)) →
    Foundations.PairUnitExponents.theta φ 0 - (Foundations.PairUnitExponents.theta φ 0 + Foundations.PairUnitExponents.theta φ 1 + Foundations.PairUnitExponents.theta φ 2) / 3 ≤ 3 / 2 - B →
    P2M.R88.Fv φ (fun _ => 1) ≤ B) →
  ∀ (n : ℕ+) (T : Semicontinuity.KTensor ℂ (fun _ : Fin 3 => n)),
    Semicontinuity.asympRank T ≤ ((n : ℕ) : ℝ) ^ B
