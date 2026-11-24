import Lib.OM.NNN8.Averaging

/-! Exact seven-symbol weight enumerators and generator averaging. As in NNN8,
noninjective generators are permitted and every nonzero message is charged. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN11
set_option maxHeartbeats 1000000

instance seven_prime : Fact (Nat.Prime 7) := ⟨by decide +kernel⟩

abbrev Word (N : ℕ) := Fin N → ZMod 7

def weight {N : ℕ} (c : Word N) : ℕ := (Finset.univ.filter (fun i => c i ≠ 0)).card

lemma word_card (N : ℕ) : Fintype.card (Word N) = 7 ^ N := by simp [Word]
lemma weight_le {N : ℕ} (c : Word N) : weight c ≤ N := by
  simpa only [Finset.card_univ, Fintype.card_fin] using!
    (Finset.card_filter_le (s := Finset.univ) (p := fun i => c i ≠ 0))
lemma weight_zero (N : ℕ) : weight (0 : Word N) = 0 := by simp [weight]

lemma weight_product {N : ℕ} (z : ℝ) (c : Word N) :
    z ^ weight c = ∏ i, if c i = 0 then 1 else z := by simp [weight, Finset.prod_ite]

theorem sum_weights (N : ℕ) (z : ℝ) : (∑ c : Word N, z ^ weight c) = (1 + 6 * z) ^ N := by
  simp only [weight_product]
  rw [← Fintype.prod_sum (fun (_ : Fin N) (b : ZMod 7) => if b = 0 then (1 : ℝ) else z)]
  have hh : (∑ b : ZMod 7, if b = 0 then (1 : ℝ) else z) = 1 + 6 * z := by
    change (∑ b : Fin 7, if b = 0 then (1 : ℝ) else z) = _
    norm_num [Fin.sum_univ_succ]
  simp [hh]

theorem exists_generator_weight_le (N r : ℕ) (z : ℝ) :
    ∃ code : Word r →ₗ[ZMod 7] Word N,
      (∑ c ∈ Finset.univ.erase (0 : Word r), z ^ weight (code c)) ≤
        ((7 : ℝ) ^ r - 1) / (7 : ℝ) ^ N * (1 + 6 * z) ^ N := by
  obtain ⟨code, hc⟩ := NNN8.exists_generator_sum_le (K := ZMod 7) (V := Word r)
    (fun c : Word N => z ^ weight c)
  refine ⟨code, ?_⟩
  simpa only [word_card, Nat.cast_pow, Nat.cast_ofNat, sum_weights] using! hc

theorem exists_generator_weight_bound (N r : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    ∃ code : Word r →ₗ[ZMod 7] Word N,
      (∑ c ∈ Finset.univ.erase (0 : Word r), z ^ weight (code c)) ≤
        (7 : ℝ) ^ r / (7 : ℝ) ^ N * (1 + 6 * z) ^ N := by
  obtain ⟨code, hc⟩ := exists_generator_weight_le N r z
  refine ⟨code, hc.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)

lemma full_residual_in_cone (l : ℕ) (c : Word (7 * l)) : 5 * (2 * weight c) ≤ 70 * l := by
  have h := weight_le c
  omega

end OM.NNN11
