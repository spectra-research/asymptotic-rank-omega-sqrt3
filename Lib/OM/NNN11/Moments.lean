import Lib.OM.NNN11.Codes
import Lib.OM.NNN11.Rounding

/-! Complete generator moments, empty message lists, and scalar normalization. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN11
set_option maxHeartbeats 1500000

def moment (N r : ℕ) (a D : ℝ) : ℝ :=
  (2 : ℝ) ^ a * (((7 : ℝ) ^ r - 1) / (7 : ℝ) ^ N * (1 + 6 * (2 : ℝ) ^ D) ^ N)

def momentExponent (N : ℕ) (a D : ℝ) : ℝ :=
  a + N * (Real.logb 2 (1 + 6 * (2 : ℝ) ^ D) - Real.logb 2 7)

lemma moment_nonneg (N r : ℕ) (a D : ℝ) : 0 ≤ moment N r a D := by
  have hp : 0 ≤ (7 : ℝ) ^ r - 1 := sub_nonneg.mpr (one_le_pow₀ (by norm_num))
  dsimp [moment]
  positivity

lemma moment_zero (N : ℕ) (a D : ℝ) : moment N 0 a D = 0 := by simp [moment]

theorem exists_generator_price (N r : ℕ) (a D : ℝ) :
    ∃ code : Word r →ₗ[ZMod 7] Word N,
      (∑ c ∈ Finset.univ.erase (0 : Word r), (2 : ℝ) ^ (a + D * weight (code c))) ≤
        moment N r a D := by
  obtain ⟨code, hc⟩ := exists_generator_weight_le N r ((2 : ℝ) ^ D)
  refine ⟨code, ?_⟩
  have he (c : Word r) : (2 : ℝ) ^ (a + D * weight (code c)) =
      (2 : ℝ) ^ a * ((2 : ℝ) ^ D) ^ weight (code c) := by
    rw [Real.rpow_add (by norm_num), Real.rpow_mul (by norm_num), Real.rpow_natCast]
  simp_rw [he]
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left hc (by positivity)

theorem moment_le (N r : ℕ) (a D : ℝ) :
    moment N r a D ≤ (2 : ℝ) ^ (momentExponent N a D + r * Real.logb 2 7) := by
  have hh : ((7 : ℝ) ^ r - 1) / (7 : ℝ) ^ N ≤ (7 : ℝ) ^ r / (7 : ℝ) ^ N :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hh
    (by positivity : 0 ≤ (1 + 6 * (2 : ℝ) ^ D) ^ N)) (by positivity : 0 ≤ (2 : ℝ) ^ a)).trans_eq
  have h7 : (7 : ℝ) = (2 : ℝ) ^ Real.logb 2 7 :=
    (Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)).symm
  have he : 1 + 6 * (2 : ℝ) ^ D = (2 : ℝ) ^ Real.logb 2 (1 + 6 * (2 : ℝ) ^ D) :=
    (Real.rpow_logb (by norm_num) (by norm_num) (by positivity)).symm
  conv_lhs => rw [he, h7]
  simp only [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [← Real.rpow_sub (by norm_num : (0 : ℝ) < 2),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  dsimp [momentExponent]
  ring

theorem moment_rounded (N : ℕ) (a D target : ℝ) :
    moment N (codeDimension 1 (max 0 (target - momentExponent N a D))) a D ≤
      (2 : ℝ) ^ target := by
  let ρ := max 0 (target - momentExponent N a D)
  by_cases hz : ρ = 0
  · change moment N (codeDimension 1 ρ) a D ≤ _
    rw [hz, codeDimension_zero, moment_zero]
    positivity
  have hρ : 0 ≤ ρ := le_max_left _ _
  have he : ρ = target - momentExponent N a D := by
    dsimp [ρ]
    apply max_eq_right
    by_contra! hn
    exact hz (max_eq_left hn.le)
  have hf := codeDimension_gain 1 hρ
  simp only [Nat.cast_one, mul_one] at hf
  refine (moment_le N _ a D).trans
    (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ?_)
  change momentExponent N a D + (codeDimension 1 ρ : ℝ) * Real.logb 2 7 ≤ target
  linarith

lemma raw_momentExponent (N d : ℕ) (S t : ℝ) :
    momentExponent N (d * S) (4 * t - 9 / 2) = d * S - N * codeK t := by
  dsimp [momentExponent, codeK]
  ring

theorem network_scalar_scaled {s v : ℝ} (hv : 0 < v)
    (h : s ^ 70 ≤ ((7 : ℝ) ^ (9 / 4 : ℝ) + 2) * v ^ 70 + s ^ 28 * v ^ 42) :
    s ≤ 2 * v := by
  apply (div_le_iff₀ hv).mp
  apply network_scalar
  rw [div_pow, div_pow]
  apply (div_le_iff₀ (pow_pos hv 70)).mpr
  have he : ((7 : ℝ) ^ (9 / 4 : ℝ) + 2 + s ^ 28 / v ^ 28) * v ^ 70 =
      ((7 : ℝ) ^ (9 / 4 : ℝ) + 2) * v ^ 70 + s ^ 28 * v ^ 42 := by
    rw [add_mul]
    congr 1
    rw [show (70 : ℕ) = 28 + 42 from rfl, pow_add, div_mul_eq_mul_div]
    field_simp
  rwa [he]

theorem network_scalar_exponent {s a : ℝ}
    (h : s ^ 70 ≤ ((7 : ℝ) ^ (9 / 4 : ℝ) + 2) * (2 : ℝ) ^ (70 * a) +
      s ^ 28 * (2 : ℝ) ^ (42 * a)) : s ≤ 2 * (2 : ℝ) ^ a := by
  apply network_scalar_scaled (by positivity)
  have he (n : ℕ) : ((2 : ℝ) ^ a) ^ n = (2 : ℝ) ^ ((n : ℝ) * a) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm]
  simpa only [he, Nat.cast_ofNat] using! h

end OM.NNN11
