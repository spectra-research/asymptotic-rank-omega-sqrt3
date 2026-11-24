import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # The two strict scalar inequalities for the rectangle in §5 -/

namespace OM.NNN34

/-- At the displacement `t = (1-a)/4`, each cost per corner is strictly
smaller than the diagonal cost per corner. -/
theorem rectangle_costs_lt {a : ℝ} (ha : 0 < a) (ha₁ : a < 1) :
    let t := (1 - a) / 4
    let s := Real.sqrt (3 + a ^ 2)
    Real.sqrt (3 * (1 - t) ^ 2 + (a - 3 * t) ^ 2) + 3 * a * t < s ∧
    Real.sqrt (3 * (1 - t) ^ 2 + a ^ 2) + 3 * t / 2 < s := by
  intro t s
  have ht : 0 < t := by dsimp [t]; linarith
  have ht₄ : 4 * t = 1 - a := by dsimp [t]; ring
  have hsq : s ^ 2 = 3 + a ^ 2 := Real.sq_sqrt (by positivity)
  have hs₁ : 1 ≤ s := Real.one_le_sqrt.mpr (by linarith [sq_nonneg a])
  have hs₂ : s ≤ 2 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    nlinarith only [mul_nonneg (sub_nonneg.mpr ha₁.le) (add_nonneg ha.le zero_le_one)]
  constructor
  · have hpos : 0 < s - 3 * a * t := by
      nlinarith only [mul_le_mul_of_nonneg_right ha₁.le ht.le, ht₄, ha, hs₁]
    have hrow : (12 - 9 * a ^ 2) * t < 6 * (1 + a - a * s) := by
      nlinarith only [ht₄, ha₁, mul_le_mul_of_nonneg_left hs₂ ha.le,
        mul_nonneg (sq_nonneg a) ht.le]
    apply lt_sub_iff_add_lt.mp
    apply (Real.sqrt_lt' hpos).mpr
    nlinarith only [hsq, mul_lt_mul_of_pos_left hrow ht]
  · have hpos : 0 < s - 3 * t / 2 := by linarith only [ht₄, ha, hs₁]
    have hcol : 3 * t / 4 < 3 * (2 - s) := by
      have hmargin : 1 - a ≤ 4 * (2 - s) := by
        nlinarith only [hsq, mul_nonneg (sub_nonneg.mpr ha₁.le) ha.le, sq_nonneg (2 - s)]
      linarith only [ht₄, ht, hmargin]
    apply lt_sub_iff_add_lt.mp
    apply (Real.sqrt_lt' hpos).mpr
    nlinarith only [hsq, mul_lt_mul_of_pos_left hcol ht]

end OM.NNN34

