import Lib.OM.NNN12.QuadraticLog
import Lib.OM.NNN12.Inner28Prices

/-! Small rational endpoint certificates for the global quadratic moment
envelopes. The logarithms are bounded by exact exponential series. -/
noncomputable section
open scoped BigOperators
namespace OM.NNN12
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

def capacityLower7 (t : ℝ) : ℝ :=
  58259 / 50000 - 271849 / 100000 * (t - 3 / 4) - 140001 / 100000 * (t - 3 / 4) ^ 2
def capacityLower11 (t : ℝ) : ℝ :=
  182610 / 100000 - 406591 / 100000 * (t - 3 / 4) - 315001 / 100000 * (t - 3 / 4) ^ 2
def momentUpper3 (D : ℝ) : ℝ := 2 / 3 * D + 7 / 80 * D ^ 2
def momentUpper19 (D : ℝ) : ℝ :=
  -136743 / 100000 + 216051 / 50000 * (D + 3 / 10) + 218751 / 100000 * (D + 3 / 10) ^ 2

lemma quadratic_exp_bounds :
    (2 : ℝ) ^ (16519 / 100000 : ℝ) ≤ 112131375 / 100000000 ∧
    (2 : ℝ) ^ (82611 / 100000 : ℝ) ≤ 177289858 / 100000000 ∧
    (2 : ℝ) ^ (36744 / 100000 : ℝ) ≤ 129006165 / 100000000 ∧
    (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 141421357 / 100000000 ∧
    (2 : ℝ) ^ (3 / 4 : ℝ) ≤ 168179284 / 100000000 := by
  refine ⟨two_rpow_upper12 (by norm_num) ?_, two_rpow_upper12 (by norm_num) ?_,
    two_rpow_upper12 (by norm_num) ?_, two_rpow_upper12 (by norm_num) ?_,
    two_rpow_upper12 (by norm_num) ?_⟩ <;>
    norm_num [expUpper12, Finset.sum_range_succ, Nat.factorial]

lemma quadratic_root_bounds :
    (14142135 / 10000000 : ℝ) ≤ (2 : ℝ) ^ (1 / 2 : ℝ) ∧
    (16817928 / 10000000 : ℝ) ≤ (2 : ℝ) ^ (3 / 4 : ℝ) := by
  constructor
  · have hh : ((2 : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = 2 := NNN11.rootTwo_sq
    have hp : 0 < (2 : ℝ) ^ (1 / 2 : ℝ) := by positivity
    nlinarith
  · have hh : ((2 : ℝ) ^ (3 / 4 : ℝ)) ^ 4 = 8 := by
      rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    apply (pow_le_pow_iff_left₀ (by norm_num : (0 : ℝ) ≤ 16817928 / 10000000)
      (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (3 / 4 : ℝ)) (by norm_num : (4 : ℕ) ≠ 0)).mp
    rw [hh]
    norm_num

lemma pow_balanced7 : (2 : ℝ) ^ (4 * (-3 / 8) : ℝ) = (2 : ℝ) ^ (1 / 2 : ℝ) / 4 := by
  rw [show (4 * (-3 / 8) : ℝ) = 1 / 2 - 2 by norm_num, Real.rpow_sub (by norm_num)]
  norm_num
lemma pow_balanced11 : (2 : ℝ) ^ (6 * (-3 / 8) : ℝ) = (2 : ℝ) ^ (3 / 4 : ℝ) / 8 := by
  rw [show (6 * (-3 / 8) : ℝ) = 3 / 4 - 3 by norm_num, Real.rpow_sub (by norm_num)]
  norm_num
lemma pow_balanced19 : (2 : ℝ) ^ (5 * (-3 / 10) : ℝ) = (2 : ℝ) ^ (1 / 2 : ℝ) / 4 := by
  rw [show (5 * (-3 / 10) : ℝ) = 1 / 2 - 2 by norm_num, Real.rpow_sub (by norm_num)]
  norm_num

lemma neg_mixedLog_ratio {q : ℝ} (hq : 1 ≤ q) (k x : ℝ) :
    -mixedLog q k x = Real.logb 2 (q / (1 + (q - 1) * (2 : ℝ) ^ (k * x))) := by
  have hq0 : 0 ≤ q - 1 := by linarith
  rw [Real.logb_div (by linarith : q ≠ 0) (by positivity)]
  dsimp [mixedLog]
  ring

lemma quadratic_capacity_centers :
    (116519 / 100000 : ℝ) ≤ -mixedLog 7 4 (-3 / 8) ∧
    (182611 / 100000 : ℝ) ≤ -mixedLog 11 6 (-3 / 8) := by
  constructor
  · rw [neg_mixedLog_ratio (by norm_num), pow_balanced7]
    apply (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) (by positivity)).2
    apply (le_div_iff₀ (by positivity : 0 < 1 + (7 - 1 : ℝ) * ((2 : ℝ) ^ (1 / 2 : ℝ) / 4))).2
    rw [show (116519 / 100000 : ℝ) = 1 + 16519 / 100000 by norm_num, Real.rpow_add (by norm_num)]
    norm_num only [Real.rpow_one]
    calc
      (2 * (2 : ℝ) ^ (16519 / 100000 : ℝ)) * (1 + 6 * ((2 : ℝ) ^ (1 / 2 : ℝ) / 4)) ≤
          (2 * (112131375 / 100000000 : ℝ)) * (1 + 6 * ((141421357 / 100000000 : ℝ) / 4)) := by
        gcongr
        · exact quadratic_exp_bounds.1
        · exact quadratic_exp_bounds.2.2.2.1
      _ ≤ 7 := by norm_num
  · rw [neg_mixedLog_ratio (by norm_num), pow_balanced11]
    apply (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) (by positivity)).2
    apply (le_div_iff₀ (by positivity : 0 < 1 + (11 - 1 : ℝ) * ((2 : ℝ) ^ (3 / 4 : ℝ) / 8))).2
    rw [show (182611 / 100000 : ℝ) = 1 + 82611 / 100000 by norm_num, Real.rpow_add (by norm_num)]
    norm_num only [Real.rpow_one]
    calc
      (2 * (2 : ℝ) ^ (82611 / 100000 : ℝ)) * (1 + 10 * ((2 : ℝ) ^ (3 / 4 : ℝ) / 8)) ≤
          (2 * (177289858 / 100000000 : ℝ)) * (1 + 10 * ((168179284 / 100000000 : ℝ) / 8)) := by
        gcongr
        · exact quadratic_exp_bounds.2.1
        · exact quadratic_exp_bounds.2.2.2.2
      _ ≤ 11 := by norm_num

lemma quadratic_moment19_center : mixedLog 19 5 (-3 / 10) ≤ -(136744 / 100000 : ℝ) := by
  have hr : mixedLog 19 5 (-3 / 10) = Real.logb 2
      ((1 + 18 * ((2 : ℝ) ^ (1 / 2 : ℝ) / 4)) / 19) := by
    rw [Real.logb_div (by positivity) (by norm_num)]
    dsimp only [mixedLog]
    rw [pow_balanced19]
    norm_num
  rw [hr]
  apply (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) (by positivity)).2
  rw [Real.rpow_neg (by norm_num), inv_eq_one_div]
  apply (le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ (136744 / 100000 : ℝ))).2
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 19)).2
  rw [show (136744 / 100000 : ℝ) = 1 + 36744 / 100000 by norm_num, Real.rpow_add (by norm_num)]
  norm_num only [Real.rpow_one, one_mul]
  calc
    (1 + 18 * ((2 : ℝ) ^ (1 / 2 : ℝ) / 4)) * (2 * (2 : ℝ) ^ (4593 / 12500 : ℝ)) ≤
        (1 + 18 * ((141421357 / 100000000 : ℝ) / 4)) * (2 * (129006165 / 100000000 : ℝ)) := by
      gcongr
      · exact quadratic_exp_bounds.2.2.2.1
      · simpa only [show (36744 / 100000 : ℝ) = 4593 / 12500 by norm_num]
          using! quadratic_exp_bounds.2.2.1
    _ ≤ 19 := by norm_num

lemma quadratic_slope_centers :
    |4 * mixedProbability 7 4 (-3 / 8) - 271849 / 100000| ≤ (1 / 50000 : ℝ) ∧
    |6 * mixedProbability 11 6 (-3 / 8) - 406591 / 100000| ≤ (1 / 50000 : ℝ) ∧
    |5 * mixedProbability 19 5 (-3 / 10) - 216051 / 50000| ≤ (1 / 50000 : ℝ) := by
  have hs0 := quadratic_root_bounds.1
  have hs1 := quadratic_exp_bounds.2.2.2.1
  have ht0 := quadratic_root_bounds.2
  have ht1 := quadratic_exp_bounds.2.2.2.2
  have h7 : mixedProbability 7 4 (-3 / 8) ∈ Set.Icc (679622 / 1000000 : ℝ) (679624 / 1000000) := by
    dsimp [mixedProbability]
    rw [pow_balanced7]
    constructor
    · apply (le_div_iff₀ (by positivity)).2; nlinarith
    · apply (div_le_iff₀ (by positivity)).2; nlinarith
  have h11 : mixedProbability 11 6 (-3 / 8) ∈ Set.Icc (677652 / 1000000 : ℝ) (677653 / 1000000) := by
    dsimp [mixedProbability]
    rw [pow_balanced11]
    constructor
    · apply (le_div_iff₀ (by positivity)).2; nlinarith
    · apply (div_le_iff₀ (by positivity)).2; nlinarith
  have h19 : mixedProbability 19 5 (-3 / 10) ∈ Set.Icc (864203 / 1000000 : ℝ) (864204 / 1000000) := by
    dsimp [mixedProbability]
    rw [pow_balanced19]
    constructor
    · apply (le_div_iff₀ (by positivity)).2; nlinarith
    · apply (div_le_iff₀ (by positivity)).2; nlinarith
  refine ⟨abs_le.mpr ⟨by linarith [h7.1], by linarith [h7.2]⟩,
    abs_le.mpr ⟨by linarith [h11.1], by linarith [h11.2]⟩,
    abs_le.mpr ⟨by linarith [h19.1], by linarith [h19.2]⟩⟩

theorem capacityLower7_le (t : ℝ) : capacityLower7 t ≤ NNN11.codeK t := by
  have hh := mixedLog_quadratic (q := 7) (by norm_num) 4 (-3 / 8) (t - 9 / 8)
  have he := rounded_slope_error (by norm_num : (0 : ℝ) ≤ 1 / 50000)
    quadratic_slope_centers.1 (x := t - 3 / 4)
  have hc := quadratic_capacity_centers.1
  have hr : -mixedLog 7 4 (t - 9 / 8) = NNN11.codeK t := by
    dsimp [mixedLog, NNN11.codeK]
    rw [show (4 * (t - 9 / 8)) = 4 * t - 9 / 2 by ring]
    norm_num
  rw [← hr]
  dsimp [capacityLower7]
  nlinarith only [hh, he, hc]

theorem capacityLower11_le (t : ℝ) : capacityLower11 t ≤ rawCapacity 11 3 t := by
  have hh := mixedLog_quadratic (q := 11) (by norm_num) 6 (-3 / 8) (t - 9 / 8)
  have he := rounded_slope_error (by norm_num : (0 : ℝ) ≤ 1 / 50000)
    quadratic_slope_centers.2.1 (x := t - 3 / 4)
  have hc := quadratic_capacity_centers.2
  have hr : -mixedLog 11 6 (t - 9 / 8) = rawCapacity 11 3 t := by
    dsimp [mixedLog, rawCapacity]
    rw [show (6 * (t - 9 / 8)) = 3 * (2 * t - 9 / 4) by ring]
    norm_num
  rw [← hr]
  dsimp [capacityLower11]
  nlinarith only [hh, he, hc]

theorem logMoment3_le_quadratic (D : ℝ) : logMoment3 D ≤ momentUpper3 D := by
  have hh := mixedLog_quadratic (q := 3) (by norm_num) 1 0 D
  norm_num [mixedLog, mixedProbability, logMoment3, momentUpper3] at hh ⊢
  exact hh

theorem logMoment19_le_quadratic (D : ℝ) : logMoment19 D ≤ momentUpper19 D := by
  have hh := mixedLog_quadratic (q := 19) (by norm_num) 5 (-3 / 10) D
  have he := rounded_slope_error (by norm_num : (0 : ℝ) ≤ 1 / 50000)
    quadratic_slope_centers.2.2 (x := D + 3 / 10)
  have hc := quadratic_moment19_center
  have hr : mixedLog 19 5 D = logMoment19 D := by norm_num [mixedLog, logMoment19]
  rw [hr] at hh
  dsimp [momentUpper19]
  nlinarith only [hh, he, hc]

end OM.NNN12
