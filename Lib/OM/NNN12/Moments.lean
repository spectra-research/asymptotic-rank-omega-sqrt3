import Lib.OM.NNN12.Codes
import Lib.OM.NNN12.Recursion

/-! Exact complete moments and legal integral rates for any prime alphabet.
This keeps finite code costs explicit before tensor-power amplification. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN12
open Codes
set_option maxHeartbeats 1500000

def moment (q N r : ℕ) (A D : ℝ) : ℝ :=
  (2 : ℝ) ^ A * (((q : ℝ) ^ r - 1) / (q : ℝ) ^ N * (1 + (q - 1 : ℝ) * (2 : ℝ) ^ D) ^ N)
def momentExponent (q N : ℕ) (A D : ℝ) : ℝ :=
  A + N * (Real.logb 2 (1 + (q - 1 : ℝ) * (2 : ℝ) ^ D) - Real.logb 2 q)
def codeDimension (q : ℕ) (ρ : ℝ) : ℕ := ⌊ρ / Real.logb 2 q⌋₊

variable {q : ℕ} [Fact q.Prime]

lemma alphabet_one_le : (1 : ℝ) ≤ q := by
  exact_mod_cast (Fact.out : Nat.Prime q).one_le
lemma alphabet_pos : (0 : ℝ) < q := by
  exact_mod_cast (Fact.out : Nat.Prime q).pos
lemma alphabet_log_pos : 0 < Real.logb 2 q := by
  apply (Real.logb_pos_iff (by norm_num : (1 : ℝ) < 2) alphabet_pos).2
  exact_mod_cast (Fact.out : Nat.Prime q).one_lt

lemma moment_nonneg (N r : ℕ) (A D : ℝ) : 0 ≤ moment q N r A D := by
  have h1 : 0 ≤ (q : ℝ) ^ r - 1 := sub_nonneg.mpr (one_le_pow₀ alphabet_one_le)
  have h2 : 0 ≤ (q - 1 : ℝ) := sub_nonneg.mpr alphabet_one_le
  have h3 := alphabet_pos (q := q)
  dsimp [moment]
  positivity

lemma moment_zero (N : ℕ) (A D : ℝ) : moment q N 0 A D = 0 := by simp [moment]

theorem exists_generator_price (N r : ℕ) (A D : ℝ) :
    ∃ code : Word q r →ₗ[ZMod q] Word q N,
      (∑ c ∈ Finset.univ.erase (0 : Word q r), (2 : ℝ) ^ (A + D * weight (code c))) ≤
        moment q N r A D := by
  obtain ⟨code, hc⟩ := NNN8.exists_generator_sum_le (K := ZMod q) (V := Word q r)
    (fun c : Word q N => (2 : ℝ) ^ (A + D * weight c))
  refine ⟨code, ?_⟩
  simpa only [word_card, Nat.cast_pow, Codes.sum_prices, moment, mul_assoc, mul_comm, mul_left_comm] using! hc

theorem moment_le (N r : ℕ) (A D : ℝ) :
    moment q N r A D ≤ (2 : ℝ) ^ (momentExponent q N A D + r * Real.logb 2 q) := by
  have hq := alphabet_pos (q := q)
  have hc : 0 ≤ (q - 1 : ℝ) := sub_nonneg.mpr alphabet_one_le
  have hh : ((q : ℝ) ^ r - 1) / (q : ℝ) ^ N ≤ (q : ℝ) ^ r / (q : ℝ) ^ N :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hh
    (by positivity : 0 ≤ (1 + (q - 1 : ℝ) * (2 : ℝ) ^ D) ^ N)) (by positivity : 0 ≤ (2 : ℝ) ^ A)).trans_eq
  have hq' : (q : ℝ) = (2 : ℝ) ^ Real.logb 2 q :=
    (Real.rpow_logb (by norm_num) (by norm_num) hq).symm
  have he : 1 + (q - 1 : ℝ) * (2 : ℝ) ^ D =
      (2 : ℝ) ^ Real.logb 2 (1 + (q - 1 : ℝ) * (2 : ℝ) ^ D) :=
    (Real.rpow_logb (by norm_num) (by norm_num) (by positivity)).symm
  conv_lhs => rw [he, hq']
  simp only [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [← Real.rpow_sub (by norm_num : (0 : ℝ) < 2),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  dsimp [momentExponent]
  rw [Real.rpow_logb (by norm_num) (by norm_num) hq]
  ring

lemma codeDimension_zero : codeDimension q 0 = 0 := by simp [codeDimension]

lemma codeDimension_le (N : ℕ) {ρ : ℝ} (hρ : ρ ≤ N * Real.logb 2 q) : codeDimension q ρ ≤ N := by
  apply Nat.floor_le_of_le
  exact (div_le_iff₀ alphabet_log_pos).2 hρ

lemma codeDimension_loss (ρ : ℝ) :
    ρ ≤ ((codeDimension q ρ : ℝ) + 1) * Real.logb 2 q := by
  have hh := mul_le_mul_of_nonneg_right (Nat.lt_floor_add_one (ρ / Real.logb 2 q)).le
    (alphabet_log_pos (q := q)).le
  rwa [div_mul_cancel₀ _ (alphabet_log_pos (q := q)).ne'] at hh

lemma codeDimension_gain {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (codeDimension q ρ : ℝ) * Real.logb 2 q ≤ ρ := by
  have hh := mul_le_mul_of_nonneg_right
    (Nat.floor_le (div_nonneg hρ (alphabet_log_pos (q := q)).le)) (alphabet_log_pos (q := q)).le
  rwa [div_mul_cancel₀ _ (alphabet_log_pos (q := q)).ne'] at hh

theorem moment_rounded (N : ℕ) (A D target : ℝ) :
    moment q N (codeDimension q (max 0 (target - momentExponent q N A D))) A D ≤ (2 : ℝ) ^ target := by
  let ρ := max 0 (target - momentExponent q N A D)
  by_cases hz : ρ = 0
  · change moment q N (codeDimension q ρ) A D ≤ _
    rw [hz, codeDimension_zero, moment_zero]
    positivity
  have hρ : 0 ≤ ρ := le_max_left _ _
  have he : ρ = target - momentExponent q N A D := by
    dsimp [ρ]
    apply max_eq_right
    by_contra! hn
    exact hz (max_eq_left hn.le)
  have hf := codeDimension_gain (q := q) hρ
  refine (moment_le N _ A D).trans
    (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ?_)
  change momentExponent q N A D + (codeDimension q ρ : ℝ) * Real.logb 2 q ≤ target
  linarith

end OM.NNN12
