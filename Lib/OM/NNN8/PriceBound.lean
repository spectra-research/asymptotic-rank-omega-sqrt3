import Lib.OM.NNN8.Codes

/-! Combine the exact tensor inequality with finite weight-enumerator averaging. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN8
open CoordinateTensor OM.NNN.Raw Foundations.PairUnitExponents
set_option maxHeartbeats 2000000

lemma dyadic_long_ge_one {l w : ℕ} (hw : w ≤ l) :
    1 ≤ ((2 : ℝ) ^ l) ^ (2 : ℕ) / (2 : ℝ) ^ w := by
  have hn : (1 : ℝ) ≤ (2 : ℝ) ^ l := one_le_pow₀ (by norm_num)
  have hd : (2 : ℝ) ^ w ≤ (2 : ℝ) ^ l := pow_le_pow_right₀ (by norm_num) hw
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ w)).2
  nlinarith

lemma dyadic_main_eq (l r : ℕ) (a t : ℝ) :
    ((2 : ℝ) ^ l) ^ a * (((2 : ℝ) ^ l) ^ (2 : ℕ) / (2 : ℝ) ^ r) ^ t =
      (2 : ℝ) ^ ((a + 2 * t) * l - t * r) := by
  rw [Real.div_rpow (by positivity) (by positivity)]
  simp only [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [← Real.rpow_sub (by norm_num : (0 : ℝ) < 2),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

lemma dyadic_correction_eq (l w : ℕ) (a t : ℝ) :
    (((2 : ℝ) ^ l) ^ (2 : ℕ) / (2 : ℝ) ^ w) ^ a * ((2 : ℝ) ^ w) ^ t =
      (2 : ℝ) ^ (2 * a * l) * ((2 : ℝ) ^ (t - a)) ^ w := by
  rw [Real.div_rpow (by positivity) (by positivity)]
  simp only [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

/-- Relax source prices coordinatewise before using the averaged enumerator.
The real `t` need not itself be a spectral parameter. -/
theorem averaged_price (φ : PolMul.Spectral ℂ) (l r : ℕ) (hr : r ≤ l)
    (T : Cube ℂ (BinaryWord l)) (t : ℝ)
    (ht : theta φ 2 ≤ t) (ha : theta φ 0 + theta φ 1 ≤ 9 / 4 - t) :
    value φ T ^ 2 ≤
      (2 : ℝ) ^ ((9 / 4 + t) * l - t * r) +
      (2 : ℝ) ^ (2 * (9 / 4 - t) * l) *
        ((2 : ℝ) ^ r / (2 : ℝ) ^ l * (1 + (2 : ℝ) ^ (2 * t - 9 / 4)) ^ l) := by
  obtain ⟨code, hcode⟩ := exists_code_weight_bound l r
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (2 * t - 9 / 4))
  have h := code_price φ l T code.toAddMonoidHom
  simp only [binary_word_card, Nat.cast_pow, Nat.cast_ofNat] at h
  have hm : ((2 : ℝ) ^ l) ^ (theta φ 0 + theta φ 1) *
      (((2 : ℝ) ^ l) ^ (2 : ℕ) / (2 : ℝ) ^ r) ^ theta φ 2 ≤
      (2 : ℝ) ^ ((9 / 4 + t) * l - t * r) := by
    have hb := mul_le_mul
      (Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (n := l) (by norm_num : (1 : ℝ) ≤ 2)) ha)
      (Real.rpow_le_rpow_of_exponent_le (dyadic_long_ge_one hr) ht)
      (by positivity) (by positivity)
    refine hb.trans_eq ?_
    rw [dyadic_main_eq]
    congr 1
    ring
  have hc (c : BinaryWord r) :
      (((2 : ℝ) ^ l) ^ (2 : ℕ) / (2 : ℝ) ^ (binaryMask (code c)).card) ^
          (theta φ 0 + theta φ 1) * ((2 : ℝ) ^ (binaryMask (code c)).card) ^ theta φ 2 ≤
        (2 : ℝ) ^ (2 * (9 / 4 - t) * l) *
          ((2 : ℝ) ^ (2 * t - 9 / 4)) ^ (binaryMask (code c)).card := by
    have hw : (binaryMask (code c)).card ≤ l := by
      simpa using! Finset.card_le_univ (binaryMask (code c))
    have hb := mul_le_mul
      (Real.rpow_le_rpow_of_exponent_le (dyadic_long_ge_one hw) ha)
      (Real.rpow_le_rpow_of_exponent_le
        (one_le_pow₀ (n := (binaryMask (code c)).card) (by norm_num : (1 : ℝ) ≤ 2)) ht)
      (by positivity) (by positivity)
    refine hb.trans_eq ?_
    rw [dyadic_correction_eq]
    congr 3
    ring
  have hcorr := Finset.sum_le_sum (fun c (_ : c ∈ Finset.univ.erase (0 : BinaryWord r)) => hc c)
  rw [← Finset.mul_sum] at hcorr
  have hcorr' := hcorr.trans
    (mul_le_mul_of_nonneg_left hcode (by positivity))
  exact h.trans (add_le_add hm hcorr')

end OM.NNN8
