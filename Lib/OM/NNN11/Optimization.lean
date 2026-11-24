import Lib.OM.NNN11.Outer
import Lib.OM.NNN11.Numerics
import Lib.OM.NNN10.Optimization
import Lib.OM.Omega

/-! Outer capacity bounds and the heavy-party choice at every spectral point.
The published omega theorem is invoked here, not assumed. -/
noncomputable section
open scoped BigOperators
namespace OM.NNN11
set_option maxHeartbeats 2000000

lemma fullMoment_antitone : AntitoneOn fullMoment (Set.Icc (1 / 4 : ℝ) 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    (fun t ht => (hasDerivAt_fullMoment (by linarith [ht.1])).continuousAt.continuousWithinAt)
    (fun t ht => (hasDerivAt_fullMoment
      (by have := interior_subset ht; linarith [this.1])).differentiableAt.differentiableWithinAt)
  intro t ht
  have ht' := interior_subset ht
  rw [(hasDerivAt_fullMoment (by linarith [ht'.1])).deriv]
  linarith [fullSlope_upper ht']

lemma lastMoment_antitone : Antitone lastMoment := by
  have hd (t : ℝ) : HasDerivAt lastMoment (-42 + 24 * codeP t) t := by
    convert! (((hasDerivAt_const t (9 / 4 : ℝ)).sub (hasDerivAt_id t)).const_mul 42).sub
      ((hasDerivAt_codeK t).const_mul 6) using 1 <;> (try dsimp [lastMoment]) <;> ring
  apply antitone_of_deriv_nonpos (fun t => (hd t).differentiableAt)
  intro t
  rw [(hd t).deriv]
  linarith [(codeP_mem t).2]

lemma innerF_one_lower : 5 / 4 ≤ innerF 1 := by
  have hk := codeK_one_bounds.2
  have hv := codeK_upper (5 / 8)
  norm_num [innerF, numeratorF, denominator, capacity, weightedK, shortParam]
  linarith

lemma innerG_one_upper : innerG 1 ≤ 9 / 8 := by
  have hc := (capacity_bounds (t := 1) (by norm_num)).1
  norm_num [innerG, numeratorG, denominator]
  linarith

lemma fullMoment_one_lower : 161 / 2 ≤ fullMoment 1 := by
  have hA : 5 / 4 ≤ outerA 1 := by dsimp [outerA]; linarith [innerF_one_lower]
  have hD : -1 ≤ 2 * outerD 1 := by dsimp [outerD]; linarith [innerG_one_upper]
  have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hD
  norm_num at hp
  have hl : 2 ≤ Real.logb 2 (1 + 6 * (2 : ℝ) ^ (2 * outerD 1)) := by
    apply (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) (by positivity)).2
    norm_num
    linarith
  dsimp [fullMoment]
  linarith [log_seven_bounds.2]

lemma lastMoment_one_lower : 49 ≤ lastMoment 1 := by
  dsimp [lastMoment]
  linarith [codeK_one_bounds.2]

theorem outer_rate_caps {b t : ℝ} (hb : b ≤ 10 / 7) (ht : t ∈ Set.Icc (1 / 4 : ℝ) 1) :
    (0 ≤ fullRate b t ∧ fullRate b t ≤ 7 * Real.logb 2 7) ∧
      (0 ≤ finalRate b t ∧ finalRate b t ≤ 6 * Real.logb 2 7) := by
  have hf := fullMoment_one_lower.trans (fullMoment_antitone ht (by norm_num) ht.2)
  have hg := lastMoment_one_lower.trans (lastMoment_antitone ht.2)
  have hl := log_seven_bounds.1
  refine ⟨⟨le_max_left _ _, max_le ?_ ?_⟩, ⟨le_max_left _ _, max_le ?_ ?_⟩⟩ <;> linarith

def chosenRate (h i : Fin 3) (t : ℝ) : ℝ :=
  if i = h then finalRate beta t else fullRate beta t

theorem exists_retained_gain (t : Fin 3 → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (1 / 4 : ℝ) 1) (hs : ∑ i, t i = 9 / 4) :
    ∃ h : Fin 3, 49 * (9 / 4) - 70 * beta ≤
      7 * t h + ∑ i, t i * chosenRate h i (t i) := by
  have hF := NNN10.jensen_three (fullWeighted_convex beta) t ht hs
  have hG := NNN10.jensen_three (lastWeighted_convex beta) t ht hs
  have hF0 : 70 * beta - fullMoment (3 / 4) ≤ fullRate beta (3 / 4) := le_max_right _ _
  have hG0 : 42 * beta - lastMoment (3 / 4) ≤ finalRate beta (3 / 4) := le_max_right _ _
  have hb := beta_balance
  simp only [Fin.sum_univ_three] at hF hG hs
  by_contra! hn
  have h0 := hn 0
  have h1 := hn 1
  have h2 := hn 2
  norm_num [Fin.sum_univ_three, chosenRate] at h0 h1 h2
  (try simp only [show ¬(2 : Fin 3) = 0 by decide +kernel,
    show ¬(2 : Fin 3) = 1 by decide +kernel,
    show ¬(0 : Fin 3) = 2 by decide +kernel,
    show ¬(1 : Fin 3) = 2 by decide +kernel, if_false] at h0 h1 h2)
  nlinarith only [h0, h1, h2, hF, hG, hF0, hG0, hs, hb]

/-- The entire numerical certificate applies to each actual complex spectral point.
No numerical top-face parameter is asserted to be an actual spectral point. -/
theorem exists_spectral_rates (φ : PolMul.Spectral ℂ) :
    ∃ (t : Fin 3 → ℝ) (h : Fin 3),
      (∀ i, Foundations.PairUnitExponents.theta φ i ≤ t i) ∧
      (∀ i, t i ∈ Set.Icc (1 / 4 : ℝ) 1) ∧ (∑ i, t i = 9 / 4) ∧
      (∀ i, 0 ≤ chosenRate h i (t i) ∧
        chosenRate h i (t i) ≤ (if i = h then 6 else 7) * Real.logb 2 7) ∧
      49 * (9 / 4) - 70 * beta ≤ 7 * t h + ∑ i, t i * chosenRate h i (t i) := by
  obtain ⟨t, hθ, ht, hs⟩ := NNN10.exists_enlargement (Foundations.PairUnitExponents.theta φ)
    (Foundations.PairUnitExponents.theta_mem_Icc φ)
    (by simpa only [Fin.sum_univ_three] using! Omega.theta_sum_le_nine_quarters φ)
  obtain ⟨h, hg⟩ := exists_retained_gain t ht hs
  refine ⟨t, h, hθ, ht, hs, ?_, hg⟩
  intro i
  have hc := outer_rate_caps beta_lt_ten_sevenths.le (ht i)
  by_cases hi : i = h
  · simpa [chosenRate, hi] using! hc.2
  · simpa [chosenRate, hi] using! hc.1

end OM.NNN11
