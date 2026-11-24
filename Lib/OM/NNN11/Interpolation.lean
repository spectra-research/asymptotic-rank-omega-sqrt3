import Lib.OM.NNN11.Functions

/-! Interpolation is an inequality on two bounds for one real value. -/
noncomputable section
namespace OM.NNN11

lemma interpolate_exponents {s a b w : ℝ} (hw : 0 ≤ w) (hw1 : w ≤ 1)
    (ha : s ≤ (2 : ℝ) ^ a) (hb : s ≤ (2 : ℝ) ^ b) :
    s ≤ (2 : ℝ) ^ ((1 - w) * a + w * b) := by
  by_cases hab : a ≤ b
  · exact ha.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith))
  · exact hb.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith))

theorem outer_interpolation {s m H t : ℝ}
    (hstar : s ≤ (2 : ℝ) ^ (m * (9 / 4 - t) + (2 * t - 9 / 4) * H))
    (hrect : s ≤ (2 : ℝ) ^ (m * innerF t + (t - innerG t) * H)) :
    s ≤ (2 : ℝ) ^ (m * outerA t + H * outerD t) := by
  apply (interpolate_exponents (w := (41 / 100 : ℝ)) (by norm_num) (by norm_num) hstar hrect).trans_eq
  congr 1
  dsimp [outerA, outerD]
  ring

end OM.NNN11
