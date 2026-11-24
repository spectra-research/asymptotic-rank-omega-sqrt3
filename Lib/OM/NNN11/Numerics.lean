import Lib.OM.NNN11.Endpoints

noncomputable section
namespace OM.NNN11
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

lemma codeK_balance_eq : codeK (3 / 4) = Real.logb 2 (7 * rootTwo / (rootTwo + 3)) := by
  have hp := rootTwo_pos.ne'
  have hd : rootTwo + 3 ≠ 0 := by linarith [rootTwo_pos]
  have hd' : 6 + rootTwo * 2 ≠ 0 := by linarith [rootTwo_pos]
  rw [codeK_eq_log_ratio]
  have he : (2 : ℝ) ^ (4 * (3 / 4) - 9 / 2 : ℝ) = 1 / (2 * rootTwo) := by
    rw [show (4 * (3 / 4) - 9 / 2 : ℝ) = -(1 + 1 / 2) by norm_num,
      Real.rpow_neg (by norm_num), Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    norm_num [rootTwo]
  rw [he]
  congr 1
  field_simp
  ring_nf
  field_simp
  ring

lemma codeK_balance_bounds : 29 / 25 ≤ codeK (3 / 4) ∧ codeK (3 / 4) ≤ 117 / 100 := by
  have hr := rootTwo_bounds
  have hp := rootTwo_pos
  have hd : 0 < rootTwo + 3 := by linarith
  have hx : 0 < 7 * rootTwo / (rootTwo + 3) := by positivity
  have hlo : (56 / 25 : ℝ) ≤ 7 * rootTwo / (rootTwo + 3) := by
    apply (le_div_iff₀ hd).2
    linarith
  have hhi : 7 * rootTwo / (rootTwo + 3) ≤ (9 / 4 : ℝ) := by
    apply (div_le_iff₀ hd).2
    linarith
  rw [codeK_balance_eq]
  constructor
  · exact (le_logb_two_of_pow_le (by norm_num : (0 : ℝ) < 56 / 25)
      (by norm_num : 0 < 25) (by norm_num : (2 : ℝ) ^ 29 ≤ (56 / 25 : ℝ) ^ 25)).trans
      ((Real.logb_le_logb (by norm_num) (by norm_num) hx).2 hlo)
  · exact ((Real.logb_le_logb (by norm_num) hx (by norm_num)).2 hhi).trans
      (logb_two_le_of_pow_le (by norm_num : (0 : ℝ) < 9 / 4)
        (by norm_num : 0 < 100) (by norm_num : (9 / 4 : ℝ) ^ 100 ≤ (2 : ℝ) ^ 117))

lemma two_rpow_neg_le_of_mul_pow {x : ℝ} (hx : 0 ≤ x) {p q : ℕ} (hq : 0 < q)
    (h : 1 ≤ x ^ q * (2 : ℝ) ^ p) : (2 : ℝ) ^ (-(p : ℝ) / q) ≤ x := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have he : ((2 : ℝ) ^ (-(p : ℝ) / q)) ^ q = 1 / (2 : ℝ) ^ p := by
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2),
      div_mul_cancel₀ _ hq', Real.rpow_neg (by norm_num), Real.rpow_natCast]
    simp
  apply (pow_le_pow_iff_left₀ (by positivity) hx hq.ne').mp
  rw [he]
  exact (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ p)).2 h

lemma logb_two_le_neg_of_mul_pow {x : ℝ} (hx : 0 < x) {p q : ℕ} (hq : 0 < q)
    (h : x ^ q * (2 : ℝ) ^ p ≤ 1) : Real.logb 2 x ≤ -(p : ℝ) / q := by
  have hh := (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2)
    (by positivity : 0 < x ^ q * (2 : ℝ) ^ p) (by norm_num)).2 h
  rw [Real.logb_mul (by positivity) (by positivity), Real.logb_pow, Real.logb_pow] at hh
  norm_num at hh
  apply (le_div_iff₀ (Nat.cast_pos.mpr hq)).2
  nlinarith

lemma outerD_balance_upper : 2 * outerD (3 / 4) ≤ -31 / 30 := by
  have hk := codeK_balance_bounds.2
  dsimp [outerD]
  rw [innerG_balance]
  linarith

lemma outer_exp_balance_upper : (2 : ℝ) ^ (2 * outerD (3 / 4)) ≤ 489 / 1000 := by
  refine (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    outerD_balance_upper).trans ?_
  exact two_rpow_neg_le_of_mul_pow (by norm_num) (by norm_num : 0 < 30)
    (by norm_num : 1 ≤ (489 / 1000 : ℝ) ^ 30 * (2 : ℝ) ^ 31)

lemma outer_log_balance_upper :
    Real.logb 2 (1 + 6 * (2 : ℝ) ^ (2 * outerD (3 / 4))) - Real.logb 2 7 ≤ -83 / 100 := by
  rw [← Real.logb_div (by positivity) (by norm_num : (7 : ℝ) ≠ 0)]
  have he : (1 + 6 * (2 : ℝ) ^ (2 * outerD (3 / 4))) / 7 ≤ 281 / 500 := by
    linarith [outer_exp_balance_upper]
  refine ((Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) (by positivity) (by norm_num)).2 he).trans ?_
  exact logb_two_le_neg_of_mul_pow (by norm_num) (by norm_num : 0 < 100)
    (by norm_num : (281 / 500 : ℝ) ^ 100 * (2 : ℝ) ^ 83 ≤ 1)

theorem beta_upper : beta ≤ 3447813 / 2436700 := by
  have hk := codeK_balance_bounds.1
  have hl := outer_log_balance_upper
  have ha : outerA (3 / 4) ≤ 3 / 2 - (41 / 100) * 30 * (29 / 25) / 413 := by
    dsimp [outerA]
    rw [innerF_balance]
    linarith
  have hb : fullMoment (3 / 4) ≤
      70 * (3 / 2 - (41 / 100) * 30 * (29 / 25) / 413) - 7 * (83 / 100) := by
    dsimp [fullMoment]
    linarith
  have hq : lastMoment (3 / 4) ≤ 63 - 6 * (29 / 25) := by
    dsimp [lastMoment]
    linarith
  dsimp [beta]
  linarith

theorem beta_lt : beta < 283 / 200 := by linarith [beta_upper]
lemma beta_lt_ten_sevenths : beta < 10 / 7 := by linarith [beta_lt]

lemma beta_nonneg : 0 ≤ beta := by
  have hk := codeK_balance_bounds
  have hp := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (2 * outerD (3 / 4))
  have hg : 0 ≤ Real.logb 2 (1 + 6 * (2 : ℝ) ^ (2 * outerD (3 / 4))) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  have ha : 0 ≤ outerA (3 / 4) - 1 := by
    dsimp [outerA]
    rw [innerF_balance]
    linarith
  have hb : 0 ≤ fullMoment (3 / 4) := by
    dsimp [fullMoment]
    linarith [log_seven_bounds.2]
  have hq : 0 ≤ lastMoment (3 / 4) := by dsimp [lastMoment]; linarith
  dsimp [beta]
  linarith

end OM.NNN11
