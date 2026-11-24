import Lib.OM.NNN8.Values
import Lib.OM.NNN8.Averaging

/-! The binary weight enumerator and the generator-matrix version of (11). -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN8
set_option maxHeartbeats 1000000

lemma weight_eq_product (l : ℕ) (z : ℝ) (w : BinaryWord l) :
    z ^ (binaryMask w).card = ∏ h, if w h = 0 then 1 else z := by
  simp [binaryMask, Finset.prod_ite]

theorem sum_binary_weights (l : ℕ) (z : ℝ) :
    (∑ w : BinaryWord l, z ^ (binaryMask w).card) = (1 + z) ^ l := by
  simp only [weight_eq_product]
  rw [← Fintype.prod_sum (fun (_ : Fin l) (b : ZMod 2) => if b = 0 then (1 : ℝ) else z)]
  have hsum : (∑ b : ZMod 2, if b = 0 then (1 : ℝ) else z) = 1 + z := by
    change (∑ b : Fin 2, if b = 0 then (1 : ℝ) else z) = _
    simp [Fin.sum_univ_two]
  simp [hsum]

/-- Some binary generator map attains the exact average, counting all nonzero
messages. The possible kernel has already been allowed in `code_price`. -/
theorem exists_code_weight_le (l r : ℕ) (z : ℝ) :
    ∃ code : BinaryWord r →ₗ[ZMod 2] BinaryWord l,
      (∑ c ∈ Finset.univ.erase (0 : BinaryWord r), z ^ (binaryMask (code c)).card) ≤
        ((2 : ℝ) ^ r - 1) / (2 : ℝ) ^ l * (1 + z) ^ l := by
  obtain ⟨code, hcode⟩ := exists_generator_sum_le (K := ZMod 2) (V := BinaryWord r)
    (fun w : BinaryWord l => z ^ (binaryMask w).card)
  refine ⟨code, ?_⟩
  simpa only [binary_word_card, Nat.cast_pow, Nat.cast_ofNat, sum_binary_weights] using! hcode

theorem exists_code_weight_bound (l r : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    ∃ code : BinaryWord r →ₗ[ZMod 2] BinaryWord l,
      (∑ c ∈ Finset.univ.erase (0 : BinaryWord r), z ^ (binaryMask (code c)).card) ≤
        (2 : ℝ) ^ r / (2 : ℝ) ^ l * (1 + z) ^ l := by
  obtain ⟨code, hcode⟩ := exists_code_weight_le l r z
  refine ⟨code, hcode.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)

end OM.NNN8
