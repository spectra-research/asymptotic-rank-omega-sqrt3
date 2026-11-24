import Lib.OM.NNN11.PermutationNetwork
import Lib.OM.NNN10.Values

/-! Exact asymmetric star prices at one spectral point, and monotone numerical
enlargement through nonnegative edge dimensions. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN11
open CoordinateTensor OM.NNN.Raw OM.NNN2 Network SlotExtraction Wiring
open Foundations.PairUnitExponents
set_option maxHeartbeats 1000000

lemma dyadic_star_price (p x y H : ℕ) (hx : H ≤ p * x) (hy : H ≤ p * y)
    (a b c : ℝ) :
    (((2 : ℝ) ^ (p * x - H)) ^ b * ((2 : ℝ) ^ H) ^ c *
      ((2 : ℝ) ^ (p * y - H)) ^ a) =
      (2 : ℝ) ^ ((p : ℝ) * (b * x + a * y) + (2 * c - (a + b + c)) * H) := by
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_natCast]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  rw [Nat.cast_sub hx, Nat.cast_sub hy]
  push_cast
  ring

lemma star_exponent_mono {p x y H : ℝ} (hx : 0 ≤ p * x - H) (hy : 0 ≤ p * y - H)
    (hH : 0 ≤ H) {a b c a' b' c' : ℝ} (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    p * (b * x + a * y) + (2 * c - (a + b + c)) * H ≤
      p * (b' * x + a' * y) + (2 * c' - (a' + b' + c')) * H := by
  have h1 := mul_le_mul_of_nonneg_left hb hx
  have h2 := mul_le_mul_of_nonneg_left ha hy
  have h3 := mul_le_mul_of_nonneg_left hc hH
  nlinarith only [h1, h2, h3]

namespace ExtractionAB
variable {A B C Z : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype Z] {x y : ℕ}
  (σ : Slot A B x y ≃ Slot A B x y) (active : Slot A B x y → Prop)

lemma equalSlots_le_X : Fintype.card (EqualSlots σ active) ≤
    (Fintype.card A + Fintype.card B + Fintype.card C) * x := by
  have h := equalSlots_le_row σ active
  simp only [Fintype.card_prod, Fintype.card_fin] at h
  exact h.trans (Nat.mul_le_mul_right x (by omega))

lemma equalSlots_le_Y : Fintype.card (EqualSlots σ active) ≤
    (Fintype.card A + Fintype.card B + Fintype.card C) * y := by
  have h := equalSlots_le_col σ active
  simp only [Fintype.card_prod, Fintype.card_fin] at h
  exact h.trans (Nat.mul_le_mul_right y (by omega))

/-- The exact star exponent uses all three original edge parameters. -/
theorem permutation_network_star_price (stable : ∀ s, active (σ s) ↔ active s)
    (fixed : ∀ s, ¬ active s → σ s = s)
    (φ : PolMul.Spectral ℂ) (T : Tensor ℂ (X x) (X y) Z)
    (Q : Operator (BondBC B C (X y) Z)) (R : Operator (BondCA C A Z (X x))) :
    value φ (Network.contract T (permutationBond σ) Q R) ≤
      (2 : ℝ) ^ ((Fintype.card A + Fintype.card B + Fintype.card C : ℕ) *
        (theta φ 1 * x + theta φ 0 * y) +
        (2 * theta φ 2 - (theta φ 0 + theta φ 1 + theta φ 2)) *
          Fintype.card (EqualSlots σ active)) := by
  have h := (value_mono φ (restricts_degenerates _ _
    (permutation_network_restriction σ active stable fixed T Q R))).trans (NNN10.value_mm_card_le φ)
  simp only [residualX_card, residualY_card, equality_card, Nat.cast_pow, Nat.cast_ofNat] at h
  rw [dyadic_star_price _ _ _ _ (equalSlots_le_X (C := C) σ active)
    (equalSlots_le_Y (C := C) σ active)] at h
  exact h

/-- Enlarging theta is justified on nonnegative logarithmic source dimensions,
even when the coefficient of the crossing count in the collected price is negative. -/
theorem permutation_network_star_enlarged (stable : ∀ s, active (σ s) ↔ active s)
    (fixed : ∀ s, ¬ active s → σ s = s)
    (φ : PolMul.Spectral ℂ) (t : Fin 3 → ℝ) (ht : ∀ i, theta φ i ≤ t i)
    (hs : t 0 + t 1 + t 2 = (9 : ℝ) / 4)
    (T : Tensor ℂ (X x) (X y) Z)
    (Q : Operator (BondBC B C (X y) Z)) (R : Operator (BondCA C A Z (X x))) :
    value φ (Network.contract T (permutationBond σ) Q R) ≤
      (2 : ℝ) ^ ((Fintype.card A + Fintype.card B + Fintype.card C : ℕ) *
        (t 1 * x + t 0 * y) + (2 * t 2 - (9 : ℝ) / 4) * Fintype.card (EqualSlots σ active)) := by
  apply (permutation_network_star_price σ active stable fixed φ T Q R).trans
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  rw [← hs]
  apply star_exponent_mono _ _ (by positivity) (ht 0) (ht 1) (ht 2)
  · apply sub_nonneg.mpr
    exact_mod_cast equalSlots_le_X (C := C) σ active
  · apply sub_nonneg.mpr
    exact_mod_cast equalSlots_le_Y (C := C) σ active

end ExtractionAB
end OM.NNN11
