import Lib.OM.NNN12.Moments

/-! A common code for complete branch sums and rounding below a common
exponent. These lemmas include zero rates and empty correction lists. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN12
open Codes
set_option maxHeartbeats 1000000

variable {q : ℕ} [Fact q.Prime]

theorem exists_generator_two_prices (N r : ℕ) (A B D E : ℝ) :
    ∃ code : Word q r →ₗ[ZMod q] Word q N,
      (∑ c ∈ Finset.univ.erase (0 : Word q r),
        ((2 : ℝ) ^ (A + D * weight (code c)) + (2 : ℝ) ^ (B + E * weight (code c)))) ≤
        moment q N r A D + moment q N r B E := by
  obtain ⟨code, hc⟩ := exists_generator_branch_sum (q := q) N r
    (![A, B] : Fin 2 → ℝ) (![D, E] : Fin 2 → ℝ)
  refine ⟨code, ?_⟩
  simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    moment, mul_add, mul_assoc, mul_comm, mul_left_comm] using! hc

lemma moment_rounded_of_le (N : ℕ) (A D M target : ℝ)
    (hM : momentExponent q N A D ≤ M) :
    moment q N (codeDimension q (max 0 (target - M))) A D ≤ (2 : ℝ) ^ target := by
  let ρ := max 0 (target - M)
  by_cases hz : ρ = 0
  · change moment q N (codeDimension q ρ) A D ≤ _
    rw [hz, codeDimension_zero, moment_zero]
    positivity
  have hρ : 0 ≤ ρ := le_max_left _ _
  have he : ρ = target - M := by
    dsimp [ρ]
    apply max_eq_right
    by_contra! hn
    exact hz (max_eq_left hn.le)
  have hf := codeDimension_gain (q := q) hρ
  apply (moment_le N _ A D).trans
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
  change momentExponent q N A D + (codeDimension q ρ : ℝ) * Real.logb 2 q ≤ target
  linarith

/-- Floors cost at most the product of the three alphabet sizes. -/
theorem rounded_head_mixed (q : Fin 3 → ℕ) [∀ i, Fact (q i).Prime]
    (L t ρ : Fin 3 → ℝ) (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) 1) (A : ℝ)
    (hh : (∑ i, t i * (L i - ρ i)) ≤ A) :
    (2 : ℝ) ^ (∑ i, t i * (L i - (codeDimension (q i) (ρ i) : ℝ) * Real.logb 2 (q i))) ≤
      (∏ i, (q i : ℝ)) * (2 : ℝ) ^ A := by
  have hi (i : Fin 3) :
      t i * (L i - (codeDimension (q i) (ρ i) : ℝ) * Real.logb 2 (q i)) ≤
        t i * (L i - ρ i) + Real.logb 2 (q i) := by
    have hf := mul_le_mul_of_nonneg_left (codeDimension_loss (q := q i) (ρ i)) (ht i).1
    have ht' := mul_le_mul_of_nonneg_right (ht i).2 (alphabet_log_pos (q := q i)).le
    nlinarith
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
  rw [Finset.sum_add_distrib] at hs
  apply (Real.rpow_le_rpow_of_exponent_le (by norm_num)
    (hs.trans (add_le_add hh le_rfl))).trans_eq
  rw [Real.rpow_add (by norm_num), Real.rpow_sum_of_pos (by norm_num)]
  simp only [Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)
    (alphabet_pos (q := q _))]
  ring

end OM.NNN12
