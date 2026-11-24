import Lib.OM.NNN11.Optimization

/-! Integral seven-ary code dimensions, floor losses, and the final scalar bound. -/
noncomputable section
open scoped BigOperators
namespace OM.NNN11
set_option maxHeartbeats 2000000

def codeDimension (l : ℕ) (ρ : ℝ) : ℕ := ⌊ρ * l / Real.logb 2 7⌋₊

lemma log_seven_pos : 0 < Real.logb 2 7 := by linarith [log_seven_bounds.1]

lemma codeDimension_zero (l : ℕ) : codeDimension l 0 = 0 := by simp [codeDimension]

theorem codeDimension_le (l b : ℕ) {ρ : ℝ} (hρ : ρ ≤ b * Real.logb 2 7) :
    codeDimension l ρ ≤ b * l := by
  apply Nat.floor_le_of_le
  apply (div_le_iff₀ log_seven_pos).2
  have h := mul_le_mul_of_nonneg_right hρ (Nat.cast_nonneg l)
  push_cast
  nlinarith

lemma codeDimension_loss (l : ℕ) (ρ : ℝ) :
    ρ * l ≤ ((codeDimension l ρ : ℝ) + 1) * Real.logb 2 7 := by
  have hh := mul_le_mul_of_nonneg_right
    (Nat.lt_floor_add_one (ρ * l / Real.logb 2 7)).le log_seven_pos.le
  rwa [div_mul_cancel₀ _ log_seven_pos.ne'] at hh

lemma codeDimension_gain (l : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (codeDimension l ρ : ℝ) * Real.logb 2 7 ≤ ρ * l := by
  have hh := mul_le_mul_of_nonneg_right
    (Nat.floor_le (div_nonneg (mul_nonneg hρ (Nat.cast_nonneg l)) log_seven_pos.le)) log_seven_pos.le
  rwa [div_mul_cancel₀ _ log_seven_pos.ne'] at hh

/-- A positive rate makes its full binomial moment affordable after rounding. -/
theorem rounded_correction_exponent (l : ℕ) {d M ρ : ℝ}
    (hρ : ρ = max 0 (d * beta - M)) (hpos : 0 < ρ) :
    M * l + (codeDimension l ρ : ℝ) * Real.logb 2 7 ≤ d * beta * l := by
  have he : ρ = d * beta - M := by
    rw [hρ] at hpos
    have hh : 0 ≤ d * beta - M := by
      by_contra! hn
      rw [max_eq_left hn.le] at hpos
      linarith
    rw [hρ, max_eq_right hh]
  have hf := codeDimension_gain l hpos.le
  rw [he] at hf ⊢
  nlinarith

/-- The head pays at most `log₂(7) * Ω` for all three floors together. -/
theorem rounded_head_exponent (l : ℕ) (t ρ : Fin 3 → ℝ) (h : Fin 3)
    (ht : ∀ i, 0 ≤ t i) (hs : ∑ i, t i = 9 / 4)
    (hg : 49 * (9 / 4) - 70 * beta ≤ 7 * t h + ∑ i, t i * ρ i) :
    (49 * (9 / 4) - 7 * t h) * l -
      (∑ i, t i * (codeDimension l (ρ i) : ℝ)) * Real.logb 2 7 ≤
      70 * beta * l + (9 / 4) * Real.logb 2 7 := by
  have hf (i) := mul_le_mul_of_nonneg_left (codeDimension_loss l (ρ i)) (ht i)
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hf i)
  have hL : (∑ i, t i * (ρ i * l)) = (∑ i, t i * ρ i) * l := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hR : (∑ i, t i * (((codeDimension l (ρ i) : ℝ) + 1) * Real.logb 2 7)) =
      ((∑ i, t i * (codeDimension l (ρ i) : ℝ)) + 9 / 4) * Real.logb 2 7 := by
    simp_rw [← mul_assoc, mul_add, mul_one]
    rw [← Finset.sum_mul, Finset.sum_add_distrib, hs]
  rw [hL, hR] at hh
  have hgm := mul_le_mul_of_nonneg_right hg (Nat.cast_nonneg l)
  nlinarith only [hh, hgm]

/-- Normalising (29) by the proposed price gives a dimension-free bound of two. -/
theorem network_scalar {x : ℝ}
    (h : x ^ 70 ≤ (7 : ℝ) ^ (9 / 4 : ℝ) + 2 + x ^ 28) : x ≤ 2 := by
  by_contra! hx
  have hx0 : 0 ≤ x := by linarith
  have hc : (7 : ℝ) ^ (9 / 4 : ℝ) ≤ 343 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 7)
      (by norm_num : (9 / 4 : ℝ) ≤ 3)
    norm_num at hh
    exact hh
  have h28 : (2 : ℝ) ^ (28 : ℕ) < x ^ 28 :=
    (pow_lt_pow_iff_left₀ (by norm_num) hx0 (by norm_num : 28 ≠ 0)).2 hx
  have h42 : (2 : ℝ) ^ (42 : ℕ) ≤ x ^ 42 := pow_le_pow_left₀ (by norm_num) hx.le 42
  have h42' : (2 : ℝ) ≤ x ^ 42 := by norm_num at h42; linarith
  have hm := mul_le_mul_of_nonneg_left h42' (pow_nonneg hx0 28)
  rw [← pow_add] at hm
  norm_num only [Nat.reduceAdd] at hm
  norm_num at h28
  nlinarith only [h, hc, h28, hm]

end OM.NNN11
