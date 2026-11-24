import Lib.OM.NNN11.ExtractionBC
import Lib.OM.NNN11.ExtractionCA
import Lib.OM.NNN11.Prices
import Lib.OM.NNN11.ValueInstances

/-! Actual rectangular dimensions and all asymmetric BC/CA prices. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN11
open CoordinateTensor OM.NNN.Raw OM.NNN2 Network SlotExtraction Wiring
open ExtractionAB (X Slot permutationBond equality_card)
open Foundations.PairUnitExponents
set_option maxHeartbeats 1000000

namespace ExtractionBC
variable {A B C V : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype V] {y z : ℕ}
  (σ : Slot B C y z ≃ Slot B C y z) (active : Slot B C y z → Prop)

theorem residualY_card : Fintype.card (ResidualY (A := A) σ active) =
    2 ^ ((Fintype.card A + Fintype.card B + Fintype.card C) * y -
      Fintype.card (EqualSlots σ active)) := by
  have h := equalSlots_le_row σ active
  simp only [Fintype.card_prod, Fintype.card_fin] at h
  simp only [ResidualY, RowRemaining, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_subtype_compl, selected_row_card,
    X, ZMod.card, Fintype.card_fin, ← pow_mul, ← pow_add]
  congr 1
  simp only [Nat.add_mul, Nat.mul_comm y]
  omega

lemma equalSlots_le_Y : Fintype.card (EqualSlots σ active) ≤
    (Fintype.card A + Fintype.card B + Fintype.card C) * y := by
  have h := equalSlots_le_row σ active
  simp only [Fintype.card_prod, Fintype.card_fin] at h
  exact h.trans (Nat.mul_le_mul_right y (by omega))

theorem residualZ_card : Fintype.card (ResidualZ (A := A) σ active) =
    2 ^ ((Fintype.card A + Fintype.card B + Fintype.card C) * z -
      Fintype.card (EqualSlots σ active)) := by
  have h := equalSlots_le_col σ active
  simp only [Fintype.card_prod, Fintype.card_fin] at h
  simp only [ResidualZ, ColRemaining, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_subtype_compl, selected_col_card,
    X, ZMod.card, Fintype.card_fin, ← pow_mul, ← pow_add]
  congr 1
  simp only [Nat.add_mul, Nat.mul_comm z]
  omega

lemma equalSlots_le_Z : Fintype.card (EqualSlots σ active) ≤
    (Fintype.card A + Fintype.card B + Fintype.card C) * z := by
  have h := equalSlots_le_col σ active
  simp only [Fintype.card_prod, Fintype.card_fin] at h
  exact h.trans (Nat.mul_le_mul_right z (by omega))

end ExtractionBC

namespace ExtractionCA
variable {A B C V : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype V] {z x : ℕ}
  (σ : Slot C A z x ≃ Slot C A z x) (active : Slot C A z x → Prop)

theorem residualZ_card : Fintype.card (ResidualZ (B := B) σ active) =
    2 ^ ((Fintype.card A + Fintype.card B + Fintype.card C) * z -
      Fintype.card (EqualSlots σ active)) := by
  have h := equalSlots_le_row σ active
  simp only [Fintype.card_prod, Fintype.card_fin] at h
  simp only [ResidualZ, RowRemaining, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_subtype_compl, selected_row_card,
    X, ZMod.card, Fintype.card_fin, ← pow_mul, ← pow_add]
  congr 1
  simp only [Nat.add_mul, Nat.mul_comm z]
  omega

lemma equalSlots_le_Z : Fintype.card (EqualSlots σ active) ≤
    (Fintype.card A + Fintype.card B + Fintype.card C) * z := by
  have h := equalSlots_le_row σ active
  simp only [Fintype.card_prod, Fintype.card_fin] at h
  exact h.trans (Nat.mul_le_mul_right z (by omega))

theorem residualX_card : Fintype.card (ResidualX (B := B) σ active) =
    2 ^ ((Fintype.card A + Fintype.card B + Fintype.card C) * x -
      Fintype.card (EqualSlots σ active)) := by
  have h := equalSlots_le_col σ active
  simp only [Fintype.card_prod, Fintype.card_fin] at h
  simp only [ResidualX, ColRemaining, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_subtype_compl, selected_col_card,
    X, ZMod.card, Fintype.card_fin, ← pow_mul, ← pow_add]
  congr 1
  simp only [Nat.add_mul, Nat.mul_comm x]
  omega

lemma equalSlots_le_X : Fintype.card (EqualSlots σ active) ≤
    (Fintype.card A + Fintype.card B + Fintype.card C) * x := by
  have h := equalSlots_le_col σ active
  simp only [Fintype.card_prod, Fintype.card_fin] at h
  exact h.trans (Nat.mul_le_mul_right x (by omega))

end ExtractionCA

namespace ExtractionBC
variable {A B C V : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype V] {y z : ℕ}
  (σ : Slot B C y z ≃ Slot B C y z) (active : Slot B C y z → Prop)

theorem permutation_network_star_price (stable : ∀ s, active (σ s) ↔ active s)
    (fixed : ∀ s, ¬ active s → σ s = s)
    (φ : PolMul.Spectral ℂ) (T : Tensor ℂ V (X y) (X z))
    (P : Operator (BondAB A B V (X y))) (R : Operator (BondCA C A (X z) V)) :
    value φ (Network.contract T P (permutationBond σ) R) ≤
      (2 : ℝ) ^ ((Fintype.card A + Fintype.card B + Fintype.card C : ℕ) *
        (theta φ 2 * y + theta φ 1 * z) +
        (2 * theta φ 0 - (theta φ 0 + theta φ 1 + theta φ 2)) *
          Fintype.card (EqualSlots σ active)) := by
  have h := (value_mono φ (restricts_degenerates _ _
    (permutation_network_restriction σ active stable fixed T P R))).trans (NNN10.value_mm_card_le φ)
  simp only [residualZ_card, residualY_card, equality_card, Nat.cast_pow, Nat.cast_ofNat] at h
  refine h.trans_eq ?_
  calc
    _ = (((2 : ℝ) ^ ((Fintype.card A + Fintype.card B + Fintype.card C) * z -
        Fintype.card (EqualSlots σ active))) ^ theta φ 1 *
      ((2 : ℝ) ^ Fintype.card (EqualSlots σ active)) ^ theta φ 0 *
      ((2 : ℝ) ^ ((Fintype.card A + Fintype.card B + Fintype.card C) * y -
        Fintype.card (EqualSlots σ active))) ^ theta φ 2) := by ring
    _ = _ := by
      rw [dyadic_star_price _ _ _ _ (equalSlots_le_Z (A := A) σ active)
        (equalSlots_le_Y (A := A) σ active)]
      congr 1
      ring

theorem permutation_network_star_enlarged (stable : ∀ s, active (σ s) ↔ active s)
    (fixed : ∀ s, ¬ active s → σ s = s)
    (φ : PolMul.Spectral ℂ) (t : Fin 3 → ℝ) (ht : ∀ i, theta φ i ≤ t i)
    (hs : t 0 + t 1 + t 2 = (9 : ℝ) / 4)
    (T : Tensor ℂ V (X y) (X z))
    (P : Operator (BondAB A B V (X y))) (R : Operator (BondCA C A (X z) V)) :
    value φ (Network.contract T P (permutationBond σ) R) ≤
      (2 : ℝ) ^ ((Fintype.card A + Fintype.card B + Fintype.card C : ℕ) *
        (t 2 * y + t 1 * z) + (2 * t 0 - (9 : ℝ) / 4) * Fintype.card (EqualSlots σ active)) := by
  apply (permutation_network_star_price σ active stable fixed φ T P R).trans
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  rw [← hs]
  have h := star_exponent_mono (a := theta φ 1) (b := theta φ 2) (c := theta φ 0)
    (a' := t 1) (b' := t 2) (c' := t 0)
    (p := (Fintype.card A + Fintype.card B + Fintype.card C : ℕ))
    (x := y) (y := z) (H := Fintype.card (EqualSlots σ active))
    (sub_nonneg.mpr (by exact_mod_cast equalSlots_le_Y (A := A) σ active))
    (sub_nonneg.mpr (by exact_mod_cast equalSlots_le_Z (A := A) σ active))
    (by positivity) (ht 1) (ht 2) (ht 0)
  nlinarith only [h]

end ExtractionBC

namespace ExtractionCA
variable {A B C V : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype V] {z x : ℕ}
  (σ : Slot C A z x ≃ Slot C A z x) (active : Slot C A z x → Prop)

theorem permutation_network_star_price (stable : ∀ s, active (σ s) ↔ active s)
    (fixed : ∀ s, ¬ active s → σ s = s)
    (φ : PolMul.Spectral ℂ) (T : Tensor ℂ (X x) V (X z))
    (P : Operator (BondAB A B (X x) V)) (Q : Operator (BondBC B C V (X z))) :
    value φ (Network.contract T P Q (permutationBond σ)) ≤
      (2 : ℝ) ^ ((Fintype.card A + Fintype.card B + Fintype.card C : ℕ) *
        (theta φ 2 * x + theta φ 0 * z) +
        (2 * theta φ 1 - (theta φ 0 + theta φ 1 + theta φ 2)) *
          Fintype.card (EqualSlots σ active)) := by
  have h := (value_mono φ (restricts_degenerates _ _
    (permutation_network_restriction σ active stable fixed T P Q))).trans (NNN10.value_mm_card_le φ)
  simp only [residualX_card, residualZ_card, equality_card, Nat.cast_pow, Nat.cast_ofNat] at h
  refine h.trans_eq ?_
  calc
    _ = (((2 : ℝ) ^ ((Fintype.card A + Fintype.card B + Fintype.card C) * x -
        Fintype.card (EqualSlots σ active))) ^ theta φ 2 *
      ((2 : ℝ) ^ Fintype.card (EqualSlots σ active)) ^ theta φ 1 *
      ((2 : ℝ) ^ ((Fintype.card A + Fintype.card B + Fintype.card C) * z -
        Fintype.card (EqualSlots σ active))) ^ theta φ 0) := by ring
    _ = _ := by
      rw [dyadic_star_price _ _ _ _ (equalSlots_le_X (B := B) σ active)
        (equalSlots_le_Z (B := B) σ active)]
      congr 1
      ring

theorem permutation_network_star_enlarged (stable : ∀ s, active (σ s) ↔ active s)
    (fixed : ∀ s, ¬ active s → σ s = s)
    (φ : PolMul.Spectral ℂ) (t : Fin 3 → ℝ) (ht : ∀ i, theta φ i ≤ t i)
    (hs : t 0 + t 1 + t 2 = (9 : ℝ) / 4)
    (T : Tensor ℂ (X x) V (X z))
    (P : Operator (BondAB A B (X x) V)) (Q : Operator (BondBC B C V (X z))) :
    value φ (Network.contract T P Q (permutationBond σ)) ≤
      (2 : ℝ) ^ ((Fintype.card A + Fintype.card B + Fintype.card C : ℕ) *
        (t 2 * x + t 0 * z) + (2 * t 1 - (9 : ℝ) / 4) * Fintype.card (EqualSlots σ active)) := by
  apply (permutation_network_star_price σ active stable fixed φ T P Q).trans
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  rw [← hs]
  have h := star_exponent_mono (a := theta φ 0) (b := theta φ 2) (c := theta φ 1)
    (a' := t 0) (b' := t 2) (c' := t 1)
    (p := (Fintype.card A + Fintype.card B + Fintype.card C : ℕ))
    (x := x) (y := z) (H := Fintype.card (EqualSlots σ active))
    (sub_nonneg.mpr (by exact_mod_cast equalSlots_le_X (B := B) σ active))
    (sub_nonneg.mpr (by exact_mod_cast equalSlots_le_Z (B := B) σ active))
    (by positivity) (ht 0) (ht 2) (ht 1)
  nlinarith only [h]

end ExtractionCA
end OM.NNN11
