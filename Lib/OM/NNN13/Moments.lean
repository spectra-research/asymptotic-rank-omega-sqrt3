import Lib.OM.NNN13.Packing
import Lib.OM.NNN12.Moments
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! Alphabet-independent analytic moment bounds. These include exact first
and second derivatives, a global curvature bound, and the bounded cost of
flooring mixed cycle counts. No sampled interval values are used. -/
noncomputable section
namespace OM.NNN13

def logMoment (q : ℕ) (d D : ℝ) : ℝ :=
  Real.logb 2 (1 + (q - 1 : ℝ) * (2 : ℝ) ^ (d * D)) - Real.logb 2 q
def probability (q : ℕ) (d D : ℝ) : ℝ :=
  (q - 1 : ℝ) * (2 : ℝ) ^ (d * D) / (1 + (q - 1 : ℝ) * (2 : ℝ) ^ (d * D))
def momentCurvature (q : ℕ) (d D : ℝ) : ℝ :=
  d ^ 2 * Real.log 2 * probability q d D * (1 - probability q d D)

variable {q : ℕ} [Fact q.Prime]

lemma probability_mem (d D : ℝ) : probability q d D ∈ Set.Icc (0 : ℝ) 1 := by
  have hq : 0 ≤ (q - 1 : ℝ) := sub_nonneg.mpr NNN12.alphabet_one_le
  have hZ : 0 ≤ (q - 1 : ℝ) * (2 : ℝ) ^ (d * D) := by positivity
  refine ⟨div_nonneg hZ (by positivity), ?_⟩
  exact (div_le_one (by positivity)).2 (by linarith)

lemma logMoment_capacity (d D : ℝ) : -Real.logb 2 q ≤ logMoment q d D := by
  have hq : 0 ≤ (q - 1 : ℝ) := sub_nonneg.mpr NNN12.alphabet_one_le
  have hh : 0 ≤ Real.logb 2 (1 + (q - 1 : ℝ) * (2 : ℝ) ^ (d * D)) :=
    Real.logb_nonneg (by norm_num) (le_add_of_nonneg_right (by positivity))
  dsimp [logMoment]
  linarith

lemma logMoment_nonpos {d D : ℝ} (hd : 0 ≤ d) (hD : D ≤ 0) : logMoment q d D ≤ 0 := by
  have hq : 0 ≤ (q - 1 : ℝ) := sub_nonneg.mpr NNN12.alphabet_one_le
  have hpow : (2 : ℝ) ^ (d * D) ≤ 1 := by
    simpa using! Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (mul_nonpos_of_nonneg_of_nonpos hd hD)
  have hb : 1 + (q - 1 : ℝ) * (2 : ℝ) ^ (d * D) ≤ q := by
    nlinarith [mul_le_mul_of_nonneg_left hpow hq]
  have hl := (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2)
    (by positivity : 0 < 1 + (q - 1 : ℝ) * (2 : ℝ) ^ (d * D))
    NNN12.alphabet_pos).2 hb
  exact sub_nonpos.mpr hl

lemma logMoment_mono {d D E : ℝ} (hd : 0 ≤ d) (hDE : D ≤ E) :
    logMoment q d D ≤ logMoment q d E := by
  have hq : 0 ≤ (q - 1 : ℝ) := sub_nonneg.mpr NNN12.alphabet_one_le
  apply sub_le_sub_right
  apply (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) (by positivity) (by positivity)).2
  have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    (mul_le_mul_of_nonneg_left hDE hd)
  nlinarith [mul_le_mul_of_nonneg_left hp hq]

lemma hasDerivAt_logMoment (d D : ℝ) :
    HasDerivAt (logMoment q d) (d * probability q d D) D := by
  have hq : 0 ≤ (q - 1 : ℝ) := sub_nonneg.mpr NNN12.alphabet_one_le
  have he : HasDerivAt (fun x : ℝ => d * x) d D := by
    simpa using! (hasDerivAt_id D).const_mul d
  have hp := (HasDerivAt.const_rpow (by norm_num : (0 : ℝ) < 2) he).const_mul (q - 1 : ℝ)
  have hl := ((hasDerivAt_const D (1 : ℝ)).add hp).log (by dsimp; positivity)
  have hn : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  convert! (hl.div_const (Real.log 2)).sub_const (Real.logb 2 q) using 1
  dsimp [probability]
  field_simp
  ring

lemma hasDerivAt_probability (d D : ℝ) :
    HasDerivAt (probability q d)
      (d * Real.log 2 * probability q d D * (1 - probability q d D)) D := by
  have hq : 0 ≤ (q - 1 : ℝ) := sub_nonneg.mpr NNN12.alphabet_one_le
  have he : HasDerivAt (fun x : ℝ => d * x) d D := by
    simpa using! (hasDerivAt_id D).const_mul d
  have hp := (HasDerivAt.const_rpow (by norm_num : (0 : ℝ) < 2) he).const_mul (q - 1 : ℝ)
  have hden : 1 + (q - 1 : ℝ) * (2 : ℝ) ^ (d * D) ≠ 0 := by positivity
  convert! hp.div ((hasDerivAt_const D (1 : ℝ)).add hp) hden using 1
  dsimp [probability]
  field_simp
  ring

lemma hasDerivAt_logMomentSlope (d D : ℝ) :
    HasDerivAt (fun x => d * probability q d x) (momentCurvature q d D) D := by
  convert! (hasDerivAt_probability (q := q) d D).const_mul d using 1 <;>
    (try dsimp [momentCurvature]) <;> ring

lemma logMomentSlope_bounds {d : ℝ} (hd : 0 ≤ d) (D : ℝ) :
    0 ≤ d * probability q d D ∧ d * probability q d D ≤ d := by
  obtain ⟨hp, hp1⟩ := probability_mem (q := q) d D
  constructor
  · exact mul_nonneg hd hp
  · nlinarith [mul_le_mul_of_nonneg_left hp1 hd]

/-- A uniform Hessian ingredient: `L'' ≤ d² log(2)/4` on the entire real line. -/
theorem momentCurvature_bounds (d D : ℝ) :
    0 ≤ momentCurvature q d D ∧ momentCurvature q d D ≤ d ^ 2 * Real.log 2 / 4 := by
  obtain ⟨hp, hp1⟩ := probability_mem (q := q) d D
  have hc : 0 ≤ d ^ 2 * Real.log 2 := mul_nonneg (sq_nonneg d) (Real.log_pos (by norm_num)).le
  have hprod : 0 ≤ probability q d D * (1 - probability q d D) :=
    mul_nonneg hp (by linarith)
  have hquarter : probability q d D * (1 - probability q d D) ≤ 1 / 4 := by
    nlinarith [sq_nonneg (probability q d D - 1 / 2)]
  dsimp [momentCurvature]
  constructor
  · nlinarith only [mul_nonneg hc hprod]
  · nlinarith only [mul_le_mul_of_nonneg_left hquarter hc]

/-- Flooring two orientation counts costs at most two alphabet logarithms.
Capacity legality must still use the actual integer count. -/
theorem cycle_rounding_cost {N M d D : ℝ} (hMN : M ≤ N) (hloss : N ≤ M + 2)
    (hd : 0 ≤ d) (hD : D ≤ 0) :
    M * logMoment q d D ≤ N * logMoment q d D + 2 * Real.logb 2 q := by
  have hl := logMoment_capacity (q := q) d D
  have hu := logMoment_nonpos (q := q) hd hD
  have h₁ := mul_le_mul_of_nonneg_left (show -logMoment q d D ≤ Real.logb 2 q by linarith)
    (sub_nonneg.mpr hMN)
  have h₂ := mul_le_mul_of_nonneg_right (show N - M ≤ 2 by linarith)
    (NNN12.alphabet_log_pos (q := q)).le
  nlinarith only [h₁, h₂]

end OM.NNN13
