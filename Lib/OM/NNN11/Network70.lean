import Lib.OM.NNN11.PermutationCodes
import Lib.OM.NNN11.Prices
import Lib.OM.NNN11.Telescope
import Lib.OM.NNN11.ValueInstances
import Lib.OM.NNN11.RetainedPrice

/-! Concrete 21/21/28 physical bond kernels. The heavy party is C; the
coordinates of the original tensor retain their original party order. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN11.Network70
open CoordinateTensor OM.NNN.Raw OM.NNN2 Network SlotExtraction ExtractionAB BondCoordinates
set_option maxHeartbeats 500000

def AB {x y : ℕ} (c : Word (6 * min x y)) :
    Operator (BondAB (Fin 21) (Fin 21) (X x) (X y)) :=
  permutationBond (MixedCrossings.permutation (lightLayout x y) c)

def BC {y z : ℕ} (c : Word (7 * min y z)) :
    Operator (BondBC (Fin 21) (Fin 28) (X y) (X z)) :=
  permutationBond (MixedCrossings.permutation (heavyLayout y z) c)

def CA {z x : ℕ} (c : Word (7 * min z x)) :
    Operator (BondCA (Fin 28) (Fin 21) (X z) (X x)) :=
  permutationBond (MixedCrossings.permutation (reverseHeavyLayout z x) c)

lemma AB_zero (x y : ℕ) : AB (x := x) (y := y) 0 = Network.identity _ := by
  rw [AB, MixedCrossings.permutation_zero, permutationBond_refl]

lemma BC_zero (y z : ℕ) : BC (y := y) (z := z) 0 = Network.identity _ := by
  rw [BC, MixedCrossings.permutation_zero, permutationBond_refl]

lemma CA_zero (z x : ℕ) : CA (z := z) (x := x) 0 = Network.identity _ := by
  rw [CA, MixedCrossings.permutation_zero, permutationBond_refl]

theorem AB_factorization {x y r : ℕ} (code : Word r →ₗ[ZMod 7] Word (6 * min x y)) :
    ∃ (χ : AddChar (Word r) ℂ) (R : ℕ)
      (U V : Fin R → BondAB (Fin 21) (Fin 21) (X x) (X y) → ℂ),
      R * 7 ^ r ≤ 2 ^ (21 * y + 21 * x) ∧
      ∀ u v, (∑ p, U p u * V p v) = Network.identity _ u v +
        ∑ c ∈ Finset.univ.erase (0 : Word r), χ c * AB (code c) u v := by
  obtain ⟨χ, R, U, V, hR, hUV⟩ := exists_network_factorization (lightLayout x y) code
  refine ⟨χ, R, U, V, ?_, hUV⟩
  simpa only [bondAB_card, Fintype.card_fin, X, Fintype.card_fun, ZMod.card,
    ← pow_mul, ← pow_add, Nat.mul_comm y 21, Nat.mul_comm x 21] using! hR

theorem BC_factorization {y z r : ℕ} (code : Word r →ₗ[ZMod 7] Word (7 * min y z)) :
    ∃ (χ : AddChar (Word r) ℂ) (R : ℕ)
      (U V : Fin R → BondBC (Fin 21) (Fin 28) (X y) (X z) → ℂ),
      R * 7 ^ r ≤ 2 ^ (21 * z + 28 * y) ∧
      ∀ u v, (∑ p, U p u * V p v) = Network.identity _ u v +
        ∑ c ∈ Finset.univ.erase (0 : Word r), χ c * BC (code c) u v := by
  obtain ⟨χ, R, U, V, hR, hUV⟩ := exists_network_factorization (heavyLayout y z) code
  refine ⟨χ, R, U, V, ?_, hUV⟩
  simpa only [bondAB_card, Fintype.card_fin, X, Fintype.card_fun, ZMod.card,
    ← pow_mul, ← pow_add, Nat.mul_comm z 21, Nat.mul_comm y 28] using! hR

theorem CA_factorization {z x r : ℕ} (code : Word r →ₗ[ZMod 7] Word (7 * min z x)) :
    ∃ (χ : AddChar (Word r) ℂ) (R : ℕ)
      (U V : Fin R → BondCA (Fin 28) (Fin 21) (X z) (X x) → ℂ),
      R * 7 ^ r ≤ 2 ^ (28 * x + 21 * z) ∧
      ∀ u v, (∑ p, U p u * V p v) = Network.identity _ u v +
        ∑ c ∈ Finset.univ.erase (0 : Word r), χ c * CA (code c) u v := by
  obtain ⟨χ, R, U, V, hR, hUV⟩ := exists_network_factorization (reverseHeavyLayout z x) code
  refine ⟨χ, R, U, V, ?_, hUV⟩
  simpa only [bondAB_card, Fintype.card_fin, X, Fintype.card_fun, ZMod.card,
    ← pow_mul, ← pow_add, Nat.mul_comm x 28, Nat.mul_comm z 21] using! hR

theorem AB_star_price {x y z : ℕ} (c : Word (6 * min x y))
    (φ : PolMul.Spectral ℂ) (T : Tensor ℂ (X x) (X y) (X z))
    (Q : Operator (BondBC (Fin 21) (Fin 28) (X y) (X z)))
    (R : Operator (BondCA (Fin 28) (Fin 21) (X z) (X x))) :
    value φ (Network.contract T (AB c) Q R) ≤
      (2 : ℝ) ^ (70 * (Foundations.PairUnitExponents.theta φ 1 * x +
        Foundations.PairUnitExponents.theta φ 0 * y) +
        (2 * Foundations.PairUnitExponents.theta φ 2 -
          (Foundations.PairUnitExponents.theta φ 0 + Foundations.PairUnitExponents.theta φ 1 +
            Foundations.PairUnitExponents.theta φ 2)) * (2 * weight c)) := by
  have h := permutation_network_star_price
    (MixedCrossings.permutation (lightLayout x y) c) (MixedCrossings.active (lightLayout x y) c)
    (MixedCrossings.stable (lightLayout x y) c) (MixedCrossings.fixed (lightLayout x y) c)
    φ T Q R
  simp only [light_selected_card, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat] at h
  exact value_le_change_fintypes φ _ h

/-- The last light/light group costs a degree-42 star times the retained
28 ordered copies of the original rectangular tensor. -/
theorem AB_retained_price {x y z : ℕ} (c : Word (6 * min x y))
    (φ : PolMul.Spectral ℂ) (T : Tensor ℂ (X x) (X y) (X z)) :
    value φ (Network.contract (C := Fin 28) T (AB c) (Network.identity _) (Network.identity _)) ≤
      (2 : ℝ) ^ (42 * (Foundations.PairUnitExponents.theta φ 1 * x +
        Foundations.PairUnitExponents.theta φ 0 * y) +
        (2 * Foundations.PairUnitExponents.theta φ 2 -
          (Foundations.PairUnitExponents.theta φ 0 + Foundations.PairUnitExponents.theta φ 1 +
            Foundations.PairUnitExponents.theta φ 2)) * (2 * weight c)) * value φ T ^ 28 := by
  have h := retained_star_price (C := Fin 28)
    (MixedCrossings.permutation (lightLayout x y) c) (MixedCrossings.active (lightLayout x y) c)
    (MixedCrossings.stable (lightLayout x y) c) (MixedCrossings.fixed (lightLayout x y) c) φ T
  simp only [light_selected_card, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat] at h
  exact value_le_change_fintypes φ _ h

end OM.NNN11.Network70
