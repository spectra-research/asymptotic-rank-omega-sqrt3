import Lib.OM.NNN11.Endpoints

/-! Global analytic derivative bounds. All estimates hold on the whole interval. -/
noncomputable section
namespace OM.NNN11
set_option maxHeartbeats 2000000

lemma capacity_bounds {t : ℝ} (ht : t ∈ Set.Icc (1 / 4 : ℝ) 1) :
    0 ≤ capacity t ∧ capacity t ≤ 363 / 8 := by
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have hv := shortParam_mem ht
  have hv0 : 0 ≤ shortParam t := by linarith [hv.1]
  have hk := codeK_bounds ht
  have hkv := codeK_bounds hv
  have h1 := mul_le_mul_of_nonneg_left hk.2 ht0
  have h2 := mul_le_mul_of_nonneg_left hkv.2 hv0
  have h3 := mul_nonneg ht0 (show 0 ≤ codeK t by linarith)
  have h4 := mul_nonneg hv0 (show 0 ≤ codeK (shortParam t) by linarith)
  dsimp [capacity, weightedK]
  constructor
  · linarith
  · dsimp [shortParam] at h2
    dsimp [shortParam]
    nlinarith [ht.2]

lemma weightedKSlope_bounds {t : ℝ} (ht : t ∈ Set.Icc (1 / 4 : ℝ) 1) :
    -4 ≤ weightedKSlope t ∧ weightedKSlope t ≤ 3 := by
  have hk := codeK_bounds ht
  have hp := codeP_mem t
  have hm := mul_le_mul ht.2 hp.2 hp.1 (by norm_num : (0 : ℝ) ≤ 1)
  have h0 := mul_nonneg (show 0 ≤ t by linarith [ht.1]) hp.1
  dsimp [weightedKSlope]
  constructor <;> nlinarith

lemma capacitySlope_bounds {t : ℝ} (ht : t ∈ Set.Icc (1 / 4 : ℝ) 1) :
    -95 / 2 ≤ capacitySlope t ∧ capacitySlope t ≤ 47 := by
  have h := weightedKSlope_bounds ht
  have hv := weightedKSlope_bounds (shortParam_mem ht)
  dsimp [capacitySlope]
  constructor <;> linarith

lemma innerF_basic {t : ℝ} (ht : t ∈ Set.Icc (1 / 4 : ℝ) 1) :
    0 ≤ innerF t ∧ innerF t ≤ 2 := by
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have hc := capacity_bounds ht
  have hsq : t ^ 2 ≤ t := by nlinarith [ht.2]
  constructor
  · apply div_nonneg _ (denominator_pos ht0).le
    dsimp [numeratorF]
    nlinarith
  · apply (div_le_iff₀ (denominator_pos ht0)).2
    dsimp [numeratorF, denominator]
    nlinarith [sq_nonneg (t - 1 / 2)]

lemma innerG_basic {t : ℝ} (ht : t ∈ Set.Icc (1 / 4 : ℝ) 1) :
    0 ≤ innerG t ∧ innerG t ≤ 2 := by
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have hc := capacity_bounds ht
  have hsq : t ^ 2 ≤ t := by nlinarith [ht.2]
  constructor
  · apply div_nonneg _ (denominator_pos ht0).le
    dsimp [numeratorG]
    nlinarith
  · apply (div_le_iff₀ (denominator_pos ht0)).2
    dsimp [numeratorG, denominator]
    nlinarith [sq_nonneg t, ht.2]

lemma innerSlopes_lower_basic {t : ℝ} (ht : t ∈ Set.Icc (1 / 4 : ℝ) 1) :
    -1 ≤ innerFSlope t ∧ -1 ≤ innerGSlope t := by
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have hc := capacitySlope_bounds ht
  have hf := innerF_basic ht
  have hg := innerG_basic ht
  constructor
  · apply (le_div_iff₀ (denominator_pos ht0)).2
    dsimp [denominator]
    linarith [ht.2]
  · apply (le_div_iff₀ (denominator_pos ht0)).2
    dsimp [denominator]
    linarith [ht.2]

lemma innerSeconds_upper {t : ℝ} (ht : t ∈ Set.Icc (1 / 4 : ℝ) 1) :
    innerFSecond t ≤ -1 / 4 ∧ innerGSecond t ≤ 0 := by
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have hc := capacitySecond_bounds ht
  have hd := innerSlopes_lower_basic ht
  constructor
  · apply (div_le_iff₀ (denominator_pos ht0)).2
    dsimp [denominator]
    linarith [ht.2]
  · apply (div_le_iff₀ (denominator_pos ht0)).2
    linarith

lemma innerFSlope_antitone : AntitoneOn innerFSlope (Set.Icc (1 / 4 : ℝ) 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    (fun t ht => (hasDerivAt_innerFSlope (by linarith [ht.1])).continuousAt.continuousWithinAt)
    (fun t ht => (hasDerivAt_innerFSlope (by have := interior_subset ht; linarith [this.1])).differentiableAt.differentiableWithinAt)
  intro t ht
  have ht' := interior_subset ht
  rw [(hasDerivAt_innerFSlope (by linarith [ht'.1])).deriv]
  linarith [(innerSeconds_upper ht').1]

lemma innerGSlope_antitone : AntitoneOn innerGSlope (Set.Icc (1 / 4 : ℝ) 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    (fun t ht => (hasDerivAt_innerGSlope (by linarith [ht.1])).continuousAt.continuousWithinAt)
    (fun t ht => (hasDerivAt_innerGSlope (by have := interior_subset ht; linarith [this.1])).differentiableAt.differentiableWithinAt)
  intro t ht
  have ht' := interior_subset ht
  rw [(hasDerivAt_innerGSlope (by linarith [ht'.1])).deriv]
  exact (innerSeconds_upper ht').2

lemma capacitySlope_quarter : 115 / 4 ≤ capacitySlope (1 / 4) := by
  have h0 := codeK_quarter_lower
  have h1 := codeP_quarter_upper
  have h2 := codeK_one_bounds.2
  have h3 := codeP_one_bounds.1
  norm_num [capacitySlope, weightedKSlope, shortParam]
  linarith

lemma capacitySlope_one : capacitySlope 1 ≤ -12 := by
  have h0 := codeK_one_bounds.2
  have h1 := codeP_one_bounds.1
  have h2 := codeK_five_eighths_lower
  have h3 := (codeP_mem (5 / 8)).2
  norm_num [capacitySlope, weightedKSlope, shortParam]
  linarith

lemma innerF_quarter_lower : 5 / 4 ≤ innerF (1 / 4) := by
  have h0 := codeK_upper (1 / 4)
  have h1 := codeK_one_bounds.2
  norm_num [innerF, numeratorF, denominator, capacity, weightedK, shortParam]
  linarith

lemma innerF_one_upper : innerF 1 ≤ 3 / 2 := by
  have hc := (capacity_bounds (t := 1) (by norm_num)).1
  norm_num [innerF, numeratorF, denominator]
  linarith

lemma innerSlope_endpoints :
    innerFSlope (1 / 4) ≤ 1 / 3 ∧ -1 / 4 ≤ innerFSlope 1 ∧
      innerGSlope (1 / 4) ≤ 6 / 5 ∧ 0 ≤ innerGSlope 1 := by
  have hc0 := capacitySlope_quarter
  have hc1 := capacitySlope_one
  have hf0 := innerF_quarter_lower
  have hf1 := innerF_one_upper
  have hg0 := (innerG_basic (t := 1 / 4) (by norm_num)).1
  have hg1 := (innerG_basic (t := 1) (by norm_num)).2
  norm_num [innerFSlope, innerGSlope, denominator]
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem innerSlope_bounds {t : ℝ} (ht : t ∈ Set.Icc (1 / 4 : ℝ) 1) :
    (-1 / 4 ≤ innerFSlope t ∧ innerFSlope t ≤ 1 / 3) ∧
      (0 ≤ innerGSlope t ∧ innerGSlope t ≤ 6 / 5) := by
  have h := innerSlope_endpoints
  exact ⟨⟨h.2.1.trans (innerFSlope_antitone ht (by norm_num) ht.2),
    (innerFSlope_antitone (by norm_num) ht ht.1).trans h.1⟩,
    ⟨h.2.2.2.trans (innerGSlope_antitone ht (by norm_num) ht.2),
    (innerGSlope_antitone (by norm_num) ht ht.1).trans h.2.2.1⟩⟩

theorem innerSecond_bounds {t : ℝ} (ht : t ∈ Set.Icc (1 / 4 : ℝ) 1) :
    innerFSecond t ≤ -1 / 4 ∧ (-3 / 2 ≤ innerGSecond t ∧ innerGSecond t ≤ 0) := by
  refine ⟨(innerSeconds_upper ht).1, ?_, (innerSeconds_upper ht).2⟩
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have hc := (capacitySecond_bounds ht).2
  have hg := (innerSlope_bounds ht).2.2
  apply (le_div_iff₀ (denominator_pos ht0)).2
  dsimp [denominator]
  linarith [ht.1]

lemma capacity_endpoint_lower : 87 / 10 ≤ capacity (1 / 4) ∧ 87 / 10 ≤ capacity 1 := by
  have h0 := codeK_quarter_lower
  have h1 := codeK_one_bounds.1
  have hv := codeK_five_eighths_lower
  norm_num [capacity, weightedK, shortParam]
  constructor <;> linarith

theorem capacity_lower {t : ℝ} (ht : t ∈ Set.Icc (1 / 4 : ℝ) 1) : 87 / 10 ≤ capacity t := by
  let a : ℝ := 4 / 3 * (1 - t)
  let b : ℝ := 4 / 3 * (t - 1 / 4)
  have ha : 0 ≤ a := by dsimp [a]; linarith [ht.2]
  have hb : 0 ≤ b := by dsimp [b]; linarith [ht.1]
  have hab : a + b = 1 := by dsimp [a, b]; ring
  have ht' : a * (1 / 4) + b * 1 = t := by dsimp [a, b]; ring
  have hc := capacity_concave.2 (by norm_num : (1 / 4 : ℝ) ∈ Set.Icc (1 / 4 : ℝ) 1)
    (by norm_num : (1 : ℝ) ∈ Set.Icc (1 / 4 : ℝ) 1) ha hb hab
  simp only [smul_eq_mul, ht'] at hc
  have h0 := mul_le_mul_of_nonneg_left capacity_endpoint_lower.1 ha
  have h1 := mul_le_mul_of_nonneg_left capacity_endpoint_lower.2 hb
  nlinarith

theorem innerF_upper {t : ℝ} (ht : t ∈ Set.Icc (1 / 4 : ℝ) 1) : innerF t ≤ 73 / 50 := by
  have hc := capacity_lower ht
  apply (div_le_iff₀ (denominator_pos (by linarith [ht.1]))).2
  dsimp [numeratorF, denominator]
  nlinarith [sq_nonneg (t - 5 / 7), ht.2]

end OM.NNN11
