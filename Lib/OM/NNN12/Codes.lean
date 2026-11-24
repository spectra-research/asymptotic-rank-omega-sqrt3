import Lib.OM.NNN11.PermutationCodes

/-! Prime-alphabet generator averaging and character factors, reusing NNN8's
general averaging theorem and NNN11's actual permutation action. A single
generator controls the sum of all branches. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN12.Codes
set_option maxHeartbeats 1000000

abbrev Word (q N : ℕ) := Fin N → ZMod q

variable {q : ℕ} [Fact q.Prime]

def weight {N : ℕ} (c : Word q N) : ℕ := (Finset.univ.filter (fun i => c i ≠ 0)).card

lemma word_card (N : ℕ) : Fintype.card (Word q N) = q ^ N := by simp [Word]
lemma weight_le {N : ℕ} (c : Word q N) : weight c ≤ N := by
  simpa only [Finset.card_univ, Fintype.card_fin] using!
    (Finset.card_filter_le (s := Finset.univ) (p := fun i => c i ≠ 0))
lemma weight_zero (N : ℕ) : weight (0 : Word q N) = 0 := by simp [weight]

lemma weight_product {N : ℕ} (z : ℝ) (c : Word q N) :
    z ^ weight c = ∏ i, if c i = 0 then 1 else z := by simp [weight, Finset.prod_ite]

lemma alphabet_sum (z : ℝ) : (∑ b : ZMod q, if b = 0 then (1 : ℝ) else z) =
    1 + (q - 1 : ℝ) * z := by
  have he (b : ZMod q) : (if b = 0 then (1 : ℝ) else z) =
      z + if b = 0 then 1 - z else 0 := by split_ifs <;> ring
  simp only [he, Finset.sum_add_distrib]
  simp
  ring

theorem sum_weights (N : ℕ) (z : ℝ) :
    (∑ c : Word q N, z ^ weight c) = (1 + (q - 1 : ℝ) * z) ^ N := by
  simp only [weight_product]
  rw [← Fintype.prod_sum (fun (_ : Fin N) (b : ZMod q) => if b = 0 then (1 : ℝ) else z)]
  simp [alphabet_sum]

theorem exists_generator_weight_le (N r : ℕ) (z : ℝ) :
    ∃ code : Word q r →ₗ[ZMod q] Word q N,
      (∑ c ∈ Finset.univ.erase (0 : Word q r), z ^ weight (code c)) ≤
        ((q : ℝ) ^ r - 1) / (q : ℝ) ^ N * (1 + (q - 1 : ℝ) * z) ^ N := by
  obtain ⟨code, hc⟩ := NNN8.exists_generator_sum_le (K := ZMod q) (V := Word q r)
    (fun c : Word q N => z ^ weight c)
  refine ⟨code, ?_⟩
  simpa only [word_card, Nat.cast_pow, sum_weights] using! hc

lemma sum_prices (N : ℕ) (A D : ℝ) :
    (∑ c : Word q N, (2 : ℝ) ^ (A + D * weight c)) =
      (2 : ℝ) ^ A * (1 + (q - 1 : ℝ) * (2 : ℝ) ^ D) ^ N := by
  have he (c : Word q N) : (2 : ℝ) ^ (A + D * weight c) =
      (2 : ℝ) ^ A * ((2 : ℝ) ^ D) ^ weight c := by
    rw [Real.rpow_add (by norm_num), Real.rpow_mul (by norm_num), Real.rpow_natCast]
  simp_rw [he]
  rw [← Finset.mul_sum, sum_weights]

/-- Complete branch sums are averaged together; the chosen code is common
to every branch and the zero word is retained in each complete moment. -/
theorem exists_generator_branch_sum {B : Type} [Fintype B]
    (N r : ℕ) (A D : B → ℝ) :
    ∃ code : Word q r →ₗ[ZMod q] Word q N,
      (∑ c ∈ Finset.univ.erase (0 : Word q r), ∑ b,
        (2 : ℝ) ^ (A b + D b * weight (code c))) ≤
      ((q : ℝ) ^ r - 1) / (q : ℝ) ^ N *
        ∑ b, (2 : ℝ) ^ A b * (1 + (q - 1 : ℝ) * (2 : ℝ) ^ D b) ^ N := by
  obtain ⟨code, hc⟩ := NNN8.exists_generator_sum_le (K := ZMod q) (V := Word q r)
    (fun c : Word q N => ∑ b, (2 : ℝ) ^ (A b + D b * weight c))
  refine ⟨code, ?_⟩
  simpa only [word_card, Nat.cast_pow, Finset.sum_comm (s := Finset.univ) (t := Finset.univ),
    sum_prices] using! hc

/-- A projector rank factorization for any prime alphabet and a literal
permutation representation; zero-rank factors and dependent codes are allowed. -/
theorem exists_permutation_factorization {S E D : Type} [Fintype E]
    (e : E ≃ (S → D)) {N r : ℕ}
    (π : Word q N → S ≃ S) (hzero : π 0 = Equiv.refl S)
    (hadd : ∀ c d, π (c + d) = (π c).trans (π d))
    (code : Word q r →ₗ[ZMod q] Word q N) :
    ∃ (χ : AddChar (Word q r) ℂ) (R : ℕ) (U V : Fin R → E → ℂ),
      R * q ^ r ≤ Fintype.card E ∧
      ∀ u v, (∑ p, U p u * V p v) = NNN11.Network.identity E u v +
        ∑ c ∈ Finset.univ.erase (0 : Word q r),
          χ c * NNN11.PermutationCodes.kernel e (π (code c)) u v := by
  open NNN11.PermutationCodes in
    obtain ⟨χ, R, U, V, hR, hUV⟩ := NNN8.exists_character_factorization
      (fun c => action e (π (code c)))
      (by simp [hzero, action_refl]) (by intro a b; simp [hadd, action_trans])
    refine ⟨χ, R, U, V, ?_, ?_⟩
    · simpa only [word_card] using! hR
    · intro u v
      have hk (c : Word q r) : action e (π (code c)) (Pi.single v 1) u =
          kernel e (π (code c)) u v := by
        simp only [action, LinearMap.coe_mk, AddHom.coe_mk, Pi.single_apply]
        rw [shift_eq_iff]
        rfl
      rw [hUV]
      simp_rw [hk]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Word q r))]
      simp only [map_zero, hzero, kernel_refl, AddChar.map_zero_eq_one, one_mul]

end OM.NNN12.Codes
