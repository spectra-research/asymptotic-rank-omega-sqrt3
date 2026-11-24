import Lib.OM.NNN11.Calculus

/-! A small exact rational endpoint certificate. No interval grid is used. -/
noncomputable section
namespace OM.NNN11
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

def rootTwo : ℝ := (2 : ℝ) ^ (1 / 2 : ℝ)

lemma rootTwo_pos : 0 < rootTwo := by unfold rootTwo; positivity
lemma rootTwo_sq : rootTwo ^ 2 = 2 := by
  rw [rootTwo, ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

lemma rootTwo_bounds : 24 / 17 ≤ rootTwo ∧ rootTwo ≤ 99 / 70 := by
  have hp := rootTwo_pos
  have hs := rootTwo_sq
  constructor <;> nlinarith

lemma le_logb_two_of_pow_le {x : ℝ} (hx : 0 < x) {p q : ℕ} (hq : 0 < q)
    (h : (2 : ℝ) ^ p ≤ x ^ q) : (p : ℝ) / q ≤ Real.logb 2 x := by
  have hh := (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2)
    (by positivity) (pow_pos hx q)).2 h
  rw [Real.logb_pow, Real.logb_pow] at hh
  norm_num at hh
  exact (div_le_iff₀ (Nat.cast_pos.mpr hq)).2 (by nlinarith)

lemma logb_two_le_of_pow_le {x : ℝ} (hx : 0 < x) {p q : ℕ} (hq : 0 < q)
    (h : x ^ q ≤ (2 : ℝ) ^ p) : Real.logb 2 x ≤ (p : ℝ) / q := by
  have hh := (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2)
    (pow_pos hx q) (by positivity)).2 h
  rw [Real.logb_pow, Real.logb_pow] at hh
  norm_num at hh
  exact (le_div_iff₀ (Nat.cast_pos.mpr hq)).2 (by nlinarith)

lemma log_seven_bounds : 14 / 5 ≤ Real.logb 2 7 ∧ Real.logb 2 7 ≤ 3 := by
  constructor
  · exact le_logb_two_of_pow_le (by norm_num) (by norm_num : 0 < 5) (by norm_num)
  · exact (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) (by norm_num)).2
      (by norm_num)

lemma pow_at_one : (2 : ℝ) ^ (4 * 1 - 9 / 2 : ℝ) = 1 / rootTwo := by
  rw [show (4 * 1 - 9 / 2 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg (by norm_num)]
  simp [rootTwo]

lemma pow_at_quarter : (2 : ℝ) ^ (4 * (1 / 4) - 9 / 2 : ℝ) = 1 / (8 * rootTwo) := by
  rw [show (4 * (1 / 4) - 9 / 2 : ℝ) = -(3 + 1 / 2) by norm_num, Real.rpow_neg (by norm_num),
    Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  norm_num [rootTwo]

lemma codeK_one_eq : codeK 1 = Real.logb 2 (7 * rootTwo / (rootTwo + 6)) := by
  rw [codeK_eq_log_ratio, pow_at_one]
  congr 1
  have hp := rootTwo_pos.ne'
  field_simp

lemma codeP_one_eq : codeP 1 = 6 / (rootTwo + 6) := by
  dsimp [codeP]
  rw [pow_at_one]
  have hp := rootTwo_pos.ne'
  field_simp

lemma codeK_one_bounds : 2 / 5 ≤ codeK 1 ∧ codeK 1 ≤ 21 / 50 := by
  have hroot := rootTwo_bounds
  have hd : 0 < rootTwo + 6 := by linarith [rootTwo_pos]
  have hlo : (4 / 3 : ℝ) ≤ 7 * rootTwo / (rootTwo + 6) := by
    apply (le_div_iff₀ hd).2
    linarith
  have hhi : 7 * rootTwo / (rootTwo + 6) ≤ (167 / 125 : ℝ) := by
    apply (div_le_iff₀ hd).2
    linarith
  have hx : 0 < 7 * rootTwo / (rootTwo + 6) := by positivity
  rw [codeK_one_eq]
  constructor
  · exact (le_logb_two_of_pow_le (by norm_num : (0 : ℝ) < 4 / 3)
      (by norm_num : 0 < 5) (by norm_num : (2 : ℝ) ^ 2 ≤ (4 / 3 : ℝ) ^ 5)).trans
      ((Real.logb_le_logb (by norm_num) (by norm_num) hx).2 hlo)
  · exact ((Real.logb_le_logb (by norm_num) hx (by norm_num)).2 hhi).trans
      (logb_two_le_of_pow_le (by norm_num : (0 : ℝ) < 167 / 125)
        (by norm_num : 0 < 50) (by norm_num : (167 / 125 : ℝ) ^ 50 ≤ (2 : ℝ) ^ 21))

lemma codeP_one_bounds : 4 / 5 ≤ codeP 1 ∧ codeP 1 ≤ 5 / 6 := by
  rw [codeP_one_eq]
  have hd : 0 < rootTwo + 6 := by linarith [rootTwo_pos]
  constructor
  · apply (le_div_iff₀ hd).2
    linarith [rootTwo_bounds.2]
  · apply (div_le_iff₀ hd).2
    linarith [rootTwo_bounds.1]

lemma codeK_quarter_lower : 2 ≤ codeK (1 / 4) := by
  have hp := rootTwo_pos
  rw [codeK_eq_log_ratio, pow_at_quarter]
  apply (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) (by positivity)).2
  rw [show (2 : ℝ) ^ (2 : ℝ) = 4 by norm_num]
  apply (le_div_iff₀ (by positivity : 0 < 1 + 6 * (1 / (8 * rootTwo)))).2
  have hr : 0 < 8 * rootTwo := by positivity
  have hfrac : 6 * (1 / (8 * rootTwo)) ≤ 3 / 4 := by
    rw [mul_one_div]
    apply (div_le_iff₀ hr).2
    linarith [rootTwo_bounds.1]
  linarith

lemma codeP_quarter_upper : codeP (1 / 4) ≤ 2 / 5 := by
  have hp := rootTwo_pos
  dsimp [codeP]
  rw [pow_at_quarter]
  have hr : 0 < 8 * rootTwo := by positivity
  have hfrac : 6 * (1 / (8 * rootTwo)) ≤ 2 / 3 := by
    rw [mul_one_div]
    apply (div_le_iff₀ hr).2
    linarith [rootTwo_bounds.1]
  apply (div_le_iff₀ (by positivity : 0 < 1 + 6 * (1 / (8 * rootTwo)))).2
  linarith

lemma codeK_five_eighths : codeK (5 / 8) = Real.logb 2 (14 / 5) := by
  rw [codeK_eq_log_ratio]
  congr 1
  norm_num [show (4 * (5 / 8) - 9 / 2 : ℝ) = -(2 : ℕ) by norm_num,
    Real.rpow_neg, Real.rpow_natCast]

lemma codeK_five_eighths_lower : 37 / 25 ≤ codeK (5 / 8) := by
  rw [codeK_five_eighths]
  exact le_logb_two_of_pow_le (by norm_num) (by norm_num : 0 < 25) (by norm_num)

lemma codeK_antitone : Antitone codeK := by
  intro s t hst
  dsimp [codeK]
  apply sub_le_sub_left
  apply (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) (by positivity) (by positivity)).2
  gcongr
  norm_num

lemma codeP_monotone : Monotone codeP := by
  intro s t hst
  have hs : 0 < 1 + 6 * (2 : ℝ) ^ (4 * s - 9 / 2) := by positivity
  have ht : 0 < 1 + 6 * (2 : ℝ) ^ (4 * t - 9 / 2) := by positivity
  have he : (2 : ℝ) ^ (4 * s - 9 / 2) ≤ (2 : ℝ) ^ (4 * t - 9 / 2) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  apply (div_le_div_iff₀ hs ht).2
  nlinarith

lemma codeK_upper (t : ℝ) : codeK t ≤ 3 := by
  have hp := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (4 * t - 9 / 2)
  have hh : 0 ≤ Real.logb 2 (1 + 6 * (2 : ℝ) ^ (4 * t - 9 / 2)) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  dsimp [codeK]
  linarith [log_seven_bounds.2]

lemma codeK_bounds {t : ℝ} (ht : t ∈ Set.Icc (1 / 4 : ℝ) 1) :
    2 / 5 ≤ codeK t ∧ codeK t ≤ 3 :=
  ⟨codeK_one_bounds.1.trans (codeK_antitone ht.2), codeK_upper t⟩

lemma codeP_upper {t : ℝ} (ht : t ≤ 1) : codeP t ≤ 5 / 6 :=
  (codeP_monotone ht).trans codeP_one_bounds.2

end OM.NNN11
