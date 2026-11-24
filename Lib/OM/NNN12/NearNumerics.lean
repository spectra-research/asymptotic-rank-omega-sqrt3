import Lib.OM.NNN12.NearFunctions
import Lib.OM.NNN11.Endpoints

/-! Two exact corner estimates. Four short exponential series provide
outward rational bounds; all arithmetic is checked by the Lean kernel. -/
noncomputable section
open scoped BigOperators
namespace OM.NNN12
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

def expUpper12 (x : ℝ) : ℝ :=
  (∑ m ∈ Finset.range 12, x ^ m / m.factorial) + x ^ 12 * 13 / (479001600 * 12)

lemma exp_le_upper12 {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : Real.exp x ≤ expUpper12 x := by
  simpa only [expUpper12, show Nat.factorial 12 = 479001600 by norm_num, Nat.cast_ofNat,
    show (12 + 1 : ℝ) = 13 by norm_num] using!
    Real.exp_bound' hx.1 hx.2 (by norm_num : 0 < 12)

lemma two_rpow_upper12 {x B : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hB : expUpper12 (x * (6931471808 / 10000000000)) ≤ B) : (2 : ℝ) ^ x ≤ B := by
  rw [Real.rpow_def_of_pos (by norm_num)]
  have he : Real.log 2 * x ≤ x * (6931471808 / 10000000000) := by
    have h := mul_le_mul_of_nonneg_right Real.log_two_lt_d9.le hx.1
    nlinarith only [h]
  apply (Real.exp_le_exp.mpr he).trans
  apply (exp_le_upper12 ⟨mul_nonneg hx.1 (by norm_num), by nlinarith [hx.2]⟩).trans hB

lemma corner_exp_bounds :
    (2 : ℝ) ^ (891 / 5000 : ℝ) ≤ 113147132 / 100000000 ∧
    (2 : ℝ) ^ (601 / 1250 : ℝ) ≤ 139551731 / 100000000 ∧
    (2 : ℝ) ^ (113 / 1250 : ℝ) ≤ 106466534 / 100000000 ∧
    (2 : ℝ) ^ (326421 / 400000 : ℝ) ≤ 176058211 / 100000000 := by
  refine ⟨two_rpow_upper12 (by norm_num) ?_, two_rpow_upper12 (by norm_num) ?_,
    two_rpow_upper12 (by norm_num) ?_, two_rpow_upper12 (by norm_num) ?_⟩ <;>
    norm_num [expUpper12, Finset.sum_range_succ, Nat.factorial]

lemma corner_raw_pow : (2 : ℝ) ^ (4 * lower - 9 / 2) =
    (2 : ℝ) ^ (601 / 1250 : ℝ) / 4 := by
  rw [show 4 * lower - 9 / 2 = (601 / 1250 : ℝ) - 2 by norm_num [lower],
    Real.rpow_sub (by norm_num)]
  norm_num

lemma corner_full_pow : (2 : ℝ) ^ (5 * (upper - b - c)) =
    (2 : ℝ) ^ (326421 / 400000 : ℝ) / 4 := by
  rw [show 5 * (upper - b - c) = (326421 / 400000 : ℝ) - 2 by norm_num [upper, b, c],
    Real.rpow_sub (by norm_num)]
  norm_num

lemma corner_codeK_lower : (5891 / 5000 : ℝ) ≤ NNN11.codeK lower := by
  rw [NNN11.codeK_eq_log_ratio]
  apply (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) (by positivity)).2
  apply (le_div_iff₀ (by positivity : 0 < 1 + 6 * (2 : ℝ) ^ (4 * lower - 9 / 2))).2
  rw [corner_raw_pow, show (5891 / 5000 : ℝ) = 1 + 891 / 5000 by norm_num,
    Real.rpow_add (by norm_num)]
  norm_num only [Real.rpow_one]
  calc
    (2 * (2 : ℝ) ^ (891 / 5000 : ℝ)) * (1 + 6 * ((2 : ℝ) ^ (601 / 1250 : ℝ) / 4)) ≤
        (2 * (113147132 / 100000000 : ℝ)) * (1 + 6 * ((139551731 / 100000000 : ℝ) / 4)) := by
      gcongr
      · exact corner_exp_bounds.1
      · exact corner_exp_bounds.2.1
    _ ≤ 7 := by norm_num

lemma corner_logMoment_upper : logMoment19 (upper - b - c) ≤ -(1363 / 1250 : ℝ) := by
  have hp : 0 < (2 : ℝ) ^ (1363 / 1250 : ℝ) := by positivity
  rw [logMoment19_ratio]
  apply (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) (by positivity)).2
  rw [Real.rpow_neg (by norm_num), inv_eq_one_div]
  apply (le_div_iff₀ hp).2
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 19)).2
  rw [corner_full_pow, show (1363 / 1250 : ℝ) = 1 + 113 / 1250 by norm_num,
    Real.rpow_add (by norm_num)]
  norm_num only [Real.rpow_one, one_mul]
  calc
    (1 + 18 * ((2 : ℝ) ^ (326421 / 400000 : ℝ) / 4)) *
        (2 * (2 : ℝ) ^ (113 / 1250 : ℝ)) ≤
      (1 + 18 * ((176058211 / 100000000 : ℝ) / 4)) *
        (2 * (106466534 / 100000000 : ℝ)) := by
      gcongr
      · exact corner_exp_bounds.2.2.2
      · exact corner_exp_bounds.2.2.1
    _ ≤ 19 := by norm_num

lemma logMoment_near_lower {t : ℝ} (ht : lower ≤ t) :
    -2 ≤ logMoment19 (t - b - c) := by
  have he : (-2 : ℝ) ≤ 5 * (t - b - c) := by norm_num [lower, b, c] at *; linarith
  have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) he
  norm_num at hp
  rw [logMoment19_ratio]
  apply (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) (by positivity)).2
  norm_num
  linarith

end OM.NNN12
