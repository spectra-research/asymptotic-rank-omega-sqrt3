import Lib.OM.PolMulRect.Compat
import Lib.OM.PolMulRect.Regularity

/-! # Spectral lower bounds and continuity for the rectangular exponent -/

namespace OM.NNN36

open OmegaBound Foundations.PairUnitExponents

/-- The three opposite-edge prices can be supplied in geometric vertex order. -/
theorem theta_dot_le_omegaRect3 (φ : PolMul.Spectral ℂ) {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    a * theta φ 0 + b * theta φ 1 + c * theta φ 2 ≤ omegaRect3 ℂ a b c := by
  rw [PolMulRect.omegaRect3_eq_omegaRect]
  exact PolMulRect.theta_dot_le_omegaRect φ ha hb hc

variable {F : Type*} [Field F]

/-- Increasing each width by at most `δ` costs at most `3δ` in the exponent. -/
theorem omegaRect3_le_add {a b c a' b' c' δ : ℝ} (hδ : 0 ≤ δ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (ha' : a' ≤ a + δ) (hb' : b' ≤ b + δ) (hc' : c' ≤ c + δ) :
    omegaRect3 F a' b' c' ≤ omegaRect3 F a b c + 3 * δ := by
  simpa only [PolMulRect.omegaRect3_eq_omegaRect] using
    (PolMulRect.omegaRect_le_add (F := F) hδ ha hb hc ha' hb' hc')

theorem continuous_rectangular_cost {X : Type*} [PseudoMetricSpace X] (q₁ q₂ q₃ : X) :
    Continuous (fun z => omegaRect3 F (dist z q₁) (dist z q₂) (dist z q₃)) := by
  simpa only [PolMulRect.omegaRect3_eq_omegaRect] using
    (PolMulRect.continuous_rectangular_cost (F := F) q₁ q₂ q₃)

end OM.NNN36

