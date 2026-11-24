import Lib.OM.NNN12.Powers

/-! Finite retained-factor inequalities imply a uniform factor of two.
The constants here pay the actual three floor factors and branch sums. -/
noncomputable section
namespace OM.NNN12

theorem retained_scalar {x C : ℝ} {h m : ℕ} (hh : 0 < h) (hm : 0 < m)
    (hC : C ≤ (2 : ℝ) ^ h) (hx : x ^ (h + m) ≤ C + x ^ h) : x ≤ 2 := by
  by_contra! hn
  have hx0 : 0 ≤ x := by linarith
  have hpow : (2 : ℝ) ^ h < x ^ h :=
    (pow_lt_pow_iff_left₀ (by norm_num) hx0 (by omega : h ≠ 0)).2 hn
  have hmpow : (2 : ℝ) ≤ x ^ m := by
    have hh : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ m := pow_le_pow_right₀ (by norm_num) hm
    exact (show (2 : ℝ) ≤ (2 : ℝ) ^ m by simpa using! hh).trans
      (pow_le_pow_left₀ (by norm_num) hn.le m)
  have hprod := mul_le_mul_of_nonneg_left hmpow (pow_nonneg hx0 h)
  rw [← pow_add] at hprod
  linarith

lemma constants28 : (63 + 4 : ℝ) ≤ (2 : ℝ) ^ (14 : ℕ) := by norm_num
lemma constants112 : (847 + 2 : ℝ) ≤ (2 : ℝ) ^ (42 : ℕ) := by norm_num
lemma constants196 : (2527 + 8 : ℝ) ≤ (2 : ℝ) ^ (70 : ℕ) := by norm_num

theorem scalar28 {s : ℝ} (hs : s ^ 28 ≤ (63 + 4 : ℝ) + s ^ 14) : s ≤ 2 :=
  retained_scalar (h := 14) (m := 14) (by norm_num) (by norm_num) constants28 hs
theorem scalar112 {s : ℝ} (hs : s ^ 112 ≤ (847 + 2 : ℝ) + s ^ 42) : s ≤ 2 :=
  retained_scalar (h := 42) (m := 70) (by norm_num) (by norm_num) constants112 hs
theorem scalar196 {s : ℝ} (hs : s ^ 196 ≤ (2527 + 8 : ℝ) + s ^ 70) : s ≤ 2 :=
  retained_scalar (h := 70) (m := 126) (by norm_num) (by norm_num) constants196 hs

theorem retained_scalar_scaled {s v C : ℝ} {h m : ℕ} (hv : 0 < v)
    (hh : 0 < h) (hm : 0 < m) (hC : C ≤ (2 : ℝ) ^ h)
    (hs : s ^ (h + m) ≤ C * v ^ (h + m) + s ^ h * v ^ m) : s ≤ 2 * v := by
  apply (div_le_iff₀ hv).1
  apply retained_scalar hh hm hC
  rw [div_pow, div_pow]
  apply (div_le_iff₀ (pow_pos hv (h + m))).2
  have he : (C + s ^ h / v ^ h) * v ^ (h + m) =
      C * v ^ (h + m) + s ^ h * v ^ m := by
    rw [add_mul]
    congr 1
    rw [pow_add, div_mul_eq_mul_div]
    field_simp
  rwa [he]

theorem network196_scalar {s A : ℝ}
    (hs : s ^ 196 ≤ (2527 + 8 : ℝ) * (2 : ℝ) ^ (196 * A) +
      s ^ 70 * (2 : ℝ) ^ (126 * A)) : s ≤ 2 * (2 : ℝ) ^ A := by
  apply retained_scalar_scaled (h := 70) (m := 126) (by positivity)
    (by norm_num) (by norm_num) constants196
  have he (n : ℕ) : ((2 : ℝ) ^ A) ^ n = (2 : ℝ) ^ ((n : ℝ) * A) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm]
  simpa only [he, Nat.cast_ofNat] using! hs

end OM.NNN12
