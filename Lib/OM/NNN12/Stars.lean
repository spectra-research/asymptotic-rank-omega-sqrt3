import Lib.OM.NNN12.Excess
import Lib.OM.NNN10.Values

/-! Elementary stars at each physical party, before any recursive assumption. -/
noncomputable section
namespace OM.NNN12
open CoordinateTensor OM.NNN.Raw OM.NNN2 Foundations.PairUnitExponents
open NNN8 (BinaryWord binary_word_card)
set_option maxHeartbeats 1000000

theorem value_le_star_A (φ : PolMul.Spectral ℂ) (x : Shape) (T : DyadicTensor x)
    (t : Fin 3 → ℝ) (hθ : ∀ i, theta φ i ≤ t i) :
    value φ T ≤ (2 : ℝ) ^ (t 2 * x 1 + t 1 * x 2) := by
  have hr : Restricts (mm (BinaryWord (x 2)) Unit (BinaryWord (x 1))) T := by
    simpa using! NNN10.starBC id (fun _ => ()) id (fun _ => ()) (fun a c b => T a b c)
  have h := (value_mono φ (restricts_degenerates _ _ hr)).trans (NNN10.value_mm_card_le φ)
  simp only [binary_word_card, Fintype.card_unique, Nat.cast_one, Real.one_rpow,
    mul_one, Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)] at h
  apply h.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
  nlinarith [mul_le_mul_of_nonneg_right (hθ 1) (Nat.cast_nonneg (x 2) : (0 : ℝ) ≤ x 2),
    mul_le_mul_of_nonneg_right (hθ 2) (Nat.cast_nonneg (x 1) : (0 : ℝ) ≤ x 1)]

theorem value_le_star_B (φ : PolMul.Spectral ℂ) (x : Shape) (T : DyadicTensor x)
    (t : Fin 3 → ℝ) (hθ : ∀ i, theta φ i ≤ t i) :
    value φ T ≤ (2 : ℝ) ^ (t 2 * x 0 + t 0 * x 2) := by
  have hr : Restricts (mm Unit (BinaryWord (x 2)) (BinaryWord (x 0))) T := by
    simpa using! NNN10.starCA id (fun _ => ()) id (fun _ => ()) T
  have h := (value_mono φ (restricts_degenerates _ _ hr)).trans (NNN10.value_mm_card_le φ)
  simp only [binary_word_card, Fintype.card_unique, Nat.cast_one, Real.one_rpow,
    one_mul, Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)] at h
  apply h.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
  nlinarith [mul_le_mul_of_nonneg_right (hθ 0) (Nat.cast_nonneg (x 2) : (0 : ℝ) ≤ x 2),
    mul_le_mul_of_nonneg_right (hθ 2) (Nat.cast_nonneg (x 0) : (0 : ℝ) ≤ x 0)]

theorem value_le_star_C (φ : PolMul.Spectral ℂ) (x : Shape) (T : DyadicTensor x)
    (t : Fin 3 → ℝ) (hθ : ∀ i, theta φ i ≤ t i) :
    value φ T ≤ (2 : ℝ) ^ (t 1 * x 0 + t 0 * x 1) := by
  have hr : Restricts (mm (BinaryWord (x 0)) (BinaryWord (x 1)) Unit) T := by
    simpa using! NNN11.starAB id (fun _ => ()) id (fun _ => ()) T
  have h := (value_mono φ (restricts_degenerates _ _ hr)).trans (NNN10.value_mm_card_le φ)
  simp only [binary_word_card, Fintype.card_unique, Nat.cast_one, Real.one_rpow,
    mul_one, Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)] at h
  apply h.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
  nlinarith [mul_le_mul_of_nonneg_right (hθ 0) (Nat.cast_nonneg (x 1) : (0 : ℝ) ≤ x 1),
    mul_le_mul_of_nonneg_right (hθ 1) (Nat.cast_nonneg (x 0) : (0 : ℝ) ≤ x 0)]

end OM.NNN12
