import Lib.OM.NNN8.Scalar
import Lib.OM.NNN8.PriceBound

/-! The spectral-point-dependent rate, including the floor loss at every length. -/
noncomputable section
namespace OM.NNN8
open CoordinateTensor OM.NNN.Raw Foundations.PairUnitExponents
set_option maxHeartbeats 2000000

lemma enumerator_base (t : ℝ) :
    1 + (2 : ℝ) ^ (2 * t - 9 / 4) = (2 : ℝ) ^ (2 * t - 9 / 4 + codeG t) := by
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  have hg : (2 : ℝ) ^ codeG t = 1 + (2 : ℝ) ^ (9 / 4 - 2 * t) :=
    Real.rpow_logb (by norm_num) (by norm_num) (by positivity)
  rw [hg, mul_add, mul_one, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  norm_num
  ring

lemma averaged_correction_eq (l r : ℕ) (t : ℝ) :
    (2 : ℝ) ^ (2 * (9 / 4 - t) * l) *
      ((2 : ℝ) ^ r / (2 : ℝ) ^ l * (1 + (2 : ℝ) ^ (2 * t - 9 / 4)) ^ l) =
        (2 : ℝ) ^ ((9 / 4 - 1 + codeG t) * l + r) := by
  rw [enumerator_base]
  simp only [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [← Real.rpow_sub (by norm_num : (0 : ℝ) < 2),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

lemma rate_balances {t : ℝ} (ht : 3 / 4 ≤ t) :
    9 / 4 + t - t * codeRate t = codeExponent t ∧
      9 / 4 - 1 + codeG t + codeRate t = codeExponent t := by
  have hn : 1 + t ≠ 0 := by linarith
  dsimp [codeRate, codeExponent]
  constructor <;> field_simp <;> ring

lemma rounded_rate_le (l : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (3 / 4 : ℝ) 1) :
    ⌊codeRate t * l⌋₊ ≤ l := by
  have hρ := codeRate_mem ht
  apply Nat.floor_le_of_le
  exact mul_le_of_le_one_left (Nat.cast_nonneg l) hρ.2.le

theorem rounded_price_bound (l : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (3 / 4 : ℝ) 1) :
    (2 : ℝ) ^ ((9 / 4 + t) * l - t * ⌊codeRate t * l⌋₊) +
      (2 : ℝ) ^ ((9 / 4 - 1 + codeG t) * l + ⌊codeRate t * l⌋₊) ≤
        4 * (((2 : ℝ) ^ l) ^ alpha0) ^ (2 : ℕ) := by
  have hρ := codeRate_mem ht
  have hfloor := Nat.floor_le (mul_nonneg hρ.1.le (Nat.cast_nonneg l))
  have hround := Nat.lt_floor_add_one (codeRate t * l)
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have hmain : (9 / 4 + t) * l - t * ⌊codeRate t * l⌋₊ ≤ codeExponent t * l + 1 := by
    have hmul := mul_le_mul_of_nonneg_left hround.le ht0
    have he := congrArg (fun z : ℝ => z * l) (rate_balances ht.1).1
    nlinarith [ht.2]
  have hcorr : (9 / 4 - 1 + codeG t) * l + ⌊codeRate t * l⌋₊ ≤ codeExponent t * l := by
    have he := congrArg (fun z : ℝ => z * l) (rate_balances ht.1).2
    nlinarith only [he, hfloor]
  have hm := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hmain
  have hc := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hcorr
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one] at hm
  have he := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    (mul_le_mul_of_nonneg_right (codeExponent_le ht) (Nat.cast_nonneg l))
  have heq : (2 : ℝ) ^ (2 * alpha0 * l) = (((2 : ℝ) ^ l) ^ alpha0) ^ (2 : ℕ) := by
    simp only [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  rw [heq] at he
  nlinarith only [hm, hc, he, sq_nonneg (((2 : ℝ) ^ l) ^ alpha0)]

/-- Dyadic bound at an orientation satisfying the two relaxed parameter caps. -/
theorem third_dyadic_value (φ : PolMul.Spectral ℂ) (l : ℕ)
    (T : Cube ℂ (BinaryWord l)) {t : ℝ} (ht : t ∈ Set.Icc (3 / 4 : ℝ) 1)
    (hb : theta φ 2 ≤ t) (ha : theta φ 0 + theta φ 1 ≤ 9 / 4 - t) :
    value φ T ≤ 2 * ((2 : ℝ) ^ l) ^ alpha0 := by
  have h := averaged_price φ l ⌊codeRate t * l⌋₊ (rounded_rate_le l ht) T t hb ha
  rw [averaged_correction_eq] at h
  have hs := h.trans (rounded_price_bound l ht)
  have hp : 0 < ((2 : ℝ) ^ l) ^ alpha0 := by positivity
  nlinarith only [hs, hp, sq_nonneg (value φ T - 2 * ((2 : ℝ) ^ l) ^ alpha0)]

end OM.NNN8
