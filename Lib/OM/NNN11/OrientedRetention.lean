import Lib.OM.NNN11.OrientedPrices
import Lib.OM.NNN11.RetainedPrice

/-! Retain the copies opposite the last physical bond without changing parties. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN11
open CoordinateTensor OM.NNN.Raw OM.NNN2 Network SlotExtraction Wiring
open ExtractionAB (X Slot permutationBond)
open Foundations.PairUnitExponents
set_option maxHeartbeats 1000000

namespace ExtractionBC
variable {A B C V : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype V] {y z : ℕ}

def addEmpty (E : Type) (w : (B → E) × (C → E)) : Outputs Empty B C E :=
  (Empty.elim, w.1, w.2)

theorem pair_as_empty_network (T : Tensor ℂ V (X y) (X z)) (M : Operator (BondBC B C (X y) (X z))) :
    (fun xx yy zz => Network.contract (A := Empty) T (Network.identity _) M (Network.identity _)
      (addEmpty _ xx) (addEmpty _ yy) (addEmpty _ zz)) = Network.pairBC T M := by
  funext xx yy zz
  rw [retainedBC]
  simp [addEmpty, ordered]

variable (σ : Slot B C y z ≃ Slot B C y z) (active : Slot B C y z → Prop)

theorem pair_star_price (stable : ∀ s, active (σ s) ↔ active s)
    (fixed : ∀ s, ¬ active s → σ s = s)
    (φ : PolMul.Spectral ℂ) (T : Tensor ℂ V (X y) (X z)) :
    value φ (Network.pairBC T (permutationBond σ)) ≤
      (2 : ℝ) ^ ((Fintype.card B + Fintype.card C : ℕ) *
        (theta φ 2 * y + theta φ 1 * z) +
        (2 * theta φ 0 - (theta φ 0 + theta φ 1 + theta φ 2)) *
          Fintype.card (EqualSlots σ active)) := by
  have hr := restricts_by_coordinates
    (Network.contract (A := Empty) T (Network.identity _) (permutationBond σ) (Network.identity _))
    (addEmpty (B := B) (C := C) _) (addEmpty _) (addEmpty _)
  rw [pair_as_empty_network] at hr
  have hp := permutation_network_star_price (A := Empty) σ active stable fixed φ T
    (Network.identity _) (Network.identity _)
  simp only [Fintype.card_eq_zero, add_zero, zero_add] at hp
  exact (value_mono φ (restricts_degenerates _ _ hr)).trans hp

theorem retained_star_price [Nonempty V] [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (stable : ∀ s, active (σ s) ↔ active s) (fixed : ∀ s, ¬ active s → σ s = s)
    (φ : PolMul.Spectral ℂ) (T : Tensor ℂ V (X y) (X z)) :
    value φ (Network.contract (A := A) T (Network.identity _) (permutationBond σ) (Network.identity _)) ≤
      (2 : ℝ) ^ ((Fintype.card B + Fintype.card C : ℕ) *
        (theta φ 2 * y + theta φ 1 * z) +
        (2 * theta φ 0 - (theta φ 0 + theta φ 1 + theta φ 2)) *
          Fintype.card (EqualSlots σ active)) * value φ T ^ Fintype.card A := by
  rw [value_retainedBC]
  exact mul_le_mul_of_nonneg_right
    (value_le_change_fintypes φ _ (pair_star_price σ active stable fixed φ T))
    (pow_nonneg (φ.nonneg _) _)

theorem pair_star_enlarged (stable : ∀ s, active (σ s) ↔ active s)
    (fixed : ∀ s, ¬ active s → σ s = s)
    (φ : PolMul.Spectral ℂ) (t : Fin 3 → ℝ) (ht : ∀ i, theta φ i ≤ t i)
    (hs : t 0 + t 1 + t 2 = (9 : ℝ) / 4) (T : Tensor ℂ V (X y) (X z)) :
    value φ (Network.pairBC T (permutationBond σ)) ≤
      (2 : ℝ) ^ ((Fintype.card B + Fintype.card C : ℕ) *
        (t 2 * y + t 1 * z) +
        (2 * t 0 - (9 : ℝ) / 4) * Fintype.card (EqualSlots σ active)) := by
  have hr := restricts_by_coordinates
    (Network.contract (A := Empty) T (Network.identity _) (permutationBond σ) (Network.identity _))
    (addEmpty (B := B) (C := C) _) (addEmpty _) (addEmpty _)
  rw [pair_as_empty_network] at hr
  have hp := permutation_network_star_enlarged (A := Empty) σ active stable fixed φ t ht hs T
    (Network.identity _) (Network.identity _)
  simp only [Fintype.card_eq_zero, add_zero, zero_add] at hp
  exact (value_mono φ (restricts_degenerates _ _ hr)).trans hp

theorem retained_star_enlarged [Nonempty V] [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (stable : ∀ s, active (σ s) ↔ active s) (fixed : ∀ s, ¬ active s → σ s = s)
    (φ : PolMul.Spectral ℂ) (t : Fin 3 → ℝ) (ht : ∀ i, theta φ i ≤ t i)
    (hs : t 0 + t 1 + t 2 = (9 : ℝ) / 4) (T : Tensor ℂ V (X y) (X z)) :
    value φ (Network.contract (A := A) T (Network.identity _) (permutationBond σ) (Network.identity _)) ≤
      (2 : ℝ) ^ ((Fintype.card B + Fintype.card C : ℕ) *
        (t 2 * y + t 1 * z) +
        (2 * t 0 - (9 : ℝ) / 4) * Fintype.card (EqualSlots σ active)) *
          value φ T ^ Fintype.card A := by
  rw [value_retainedBC]
  exact mul_le_mul_of_nonneg_right
    (value_le_change_fintypes φ _ (pair_star_enlarged σ active stable fixed φ t ht hs T))
    (pow_nonneg (φ.nonneg _) _)

end ExtractionBC

namespace ExtractionCA
variable {A B C V : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype V] {z x : ℕ}

def addEmpty (E : Type) (w : (A → E) × (C → E)) : Outputs A Empty C E :=
  (w.1, Empty.elim, w.2)

theorem pair_as_empty_network (T : Tensor ℂ (X x) V (X z)) (M : Operator (BondCA C A (X z) (X x))) :
    (fun xx yy zz => Network.contract (B := Empty) T (Network.identity _) (Network.identity _) M
      (addEmpty _ xx) (addEmpty _ yy) (addEmpty _ zz)) = Network.pairCA T M := by
  funext xx yy zz
  rw [retainedCA]
  simp [addEmpty, ordered]

variable (σ : Slot C A z x ≃ Slot C A z x) (active : Slot C A z x → Prop)

theorem pair_star_price (stable : ∀ s, active (σ s) ↔ active s)
    (fixed : ∀ s, ¬ active s → σ s = s)
    (φ : PolMul.Spectral ℂ) (T : Tensor ℂ (X x) V (X z)) :
    value φ (Network.pairCA T (permutationBond σ)) ≤
      (2 : ℝ) ^ ((Fintype.card A + Fintype.card C : ℕ) *
        (theta φ 2 * x + theta φ 0 * z) +
        (2 * theta φ 1 - (theta φ 0 + theta φ 1 + theta φ 2)) *
          Fintype.card (EqualSlots σ active)) := by
  have hr := restricts_by_coordinates
    (Network.contract (B := Empty) T (Network.identity _) (Network.identity _) (permutationBond σ))
    (addEmpty (A := A) (C := C) _) (addEmpty _) (addEmpty _)
  rw [pair_as_empty_network] at hr
  have hp := permutation_network_star_price (B := Empty) σ active stable fixed φ T
    (Network.identity _) (Network.identity _)
  simp only [Fintype.card_eq_zero, add_zero, zero_add] at hp
  exact (value_mono φ (restricts_degenerates _ _ hr)).trans hp

theorem retained_star_price [Nonempty V] [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (stable : ∀ s, active (σ s) ↔ active s) (fixed : ∀ s, ¬ active s → σ s = s)
    (φ : PolMul.Spectral ℂ) (T : Tensor ℂ (X x) V (X z)) :
    value φ (Network.contract (B := B) T (Network.identity _) (Network.identity _) (permutationBond σ)) ≤
      (2 : ℝ) ^ ((Fintype.card A + Fintype.card C : ℕ) *
        (theta φ 2 * x + theta φ 0 * z) +
        (2 * theta φ 1 - (theta φ 0 + theta φ 1 + theta φ 2)) *
          Fintype.card (EqualSlots σ active)) * value φ T ^ Fintype.card B := by
  rw [value_retainedCA]
  exact mul_le_mul_of_nonneg_right
    (value_le_change_fintypes φ _ (pair_star_price σ active stable fixed φ T))
    (pow_nonneg (φ.nonneg _) _)

theorem pair_star_enlarged (stable : ∀ s, active (σ s) ↔ active s)
    (fixed : ∀ s, ¬ active s → σ s = s)
    (φ : PolMul.Spectral ℂ) (t : Fin 3 → ℝ) (ht : ∀ i, theta φ i ≤ t i)
    (hs : t 0 + t 1 + t 2 = (9 : ℝ) / 4) (T : Tensor ℂ (X x) V (X z)) :
    value φ (Network.pairCA T (permutationBond σ)) ≤
      (2 : ℝ) ^ ((Fintype.card A + Fintype.card C : ℕ) *
        (t 2 * x + t 0 * z) +
        (2 * t 1 - (9 : ℝ) / 4) * Fintype.card (EqualSlots σ active)) := by
  have hr := restricts_by_coordinates
    (Network.contract (B := Empty) T (Network.identity _) (Network.identity _) (permutationBond σ))
    (addEmpty (A := A) (C := C) _) (addEmpty _) (addEmpty _)
  rw [pair_as_empty_network] at hr
  have hp := permutation_network_star_enlarged (B := Empty) σ active stable fixed φ t ht hs T
    (Network.identity _) (Network.identity _)
  simp only [Fintype.card_eq_zero, add_zero, zero_add] at hp
  exact (value_mono φ (restricts_degenerates _ _ hr)).trans hp

theorem retained_star_enlarged [Nonempty V] [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (stable : ∀ s, active (σ s) ↔ active s) (fixed : ∀ s, ¬ active s → σ s = s)
    (φ : PolMul.Spectral ℂ) (t : Fin 3 → ℝ) (ht : ∀ i, theta φ i ≤ t i)
    (hs : t 0 + t 1 + t 2 = (9 : ℝ) / 4) (T : Tensor ℂ (X x) V (X z)) :
    value φ (Network.contract (B := B) T (Network.identity _) (Network.identity _) (permutationBond σ)) ≤
      (2 : ℝ) ^ ((Fintype.card A + Fintype.card C : ℕ) *
        (t 2 * x + t 0 * z) +
        (2 * t 1 - (9 : ℝ) / 4) * Fintype.card (EqualSlots σ active)) *
          value φ T ^ Fintype.card B := by
  rw [value_retainedCA]
  exact mul_le_mul_of_nonneg_right
    (value_le_change_fintypes φ _ (pair_star_enlarged σ active stable fixed φ t ht hs T))
    (pow_nonneg (φ.nonneg _) _)

end ExtractionCA

namespace ExtractionAB
variable {A B C Z : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype Z] {x y : ℕ}
  (σ : Slot A B x y ≃ Slot A B x y) (active : Slot A B x y → Prop)

theorem pair_star_enlarged (stable : ∀ s, active (σ s) ↔ active s)
    (fixed : ∀ s, ¬ active s → σ s = s)
    (φ : PolMul.Spectral ℂ) (t : Fin 3 → ℝ) (ht : ∀ i, theta φ i ≤ t i)
    (hs : t 0 + t 1 + t 2 = (9 : ℝ) / 4) (T : Tensor ℂ (X x) (X y) Z) :
    value φ (Network.pairAB T (permutationBond σ)) ≤
      (2 : ℝ) ^ ((Fintype.card A + Fintype.card B : ℕ) *
        (t 1 * x + t 0 * y) +
        (2 * t 2 - (9 : ℝ) / 4) * Fintype.card (EqualSlots σ active)) := by
  have hr := restricts_by_coordinates
    (Network.contract (C := Empty) T (permutationBond σ) (Network.identity _) (Network.identity _))
    (addEmpty (A := A) (B := B) _) (addEmpty _) (addEmpty _)
  rw [pairAB_as_empty_network] at hr
  have hp := permutation_network_star_enlarged (C := Empty) σ active stable fixed φ t ht hs T
    (Network.identity _) (Network.identity _)
  simp only [Fintype.card_eq_zero, add_zero] at hp
  exact (value_mono φ (restricts_degenerates _ _ hr)).trans hp

theorem retained_star_enlarged [Nonempty Z] [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (stable : ∀ s, active (σ s) ↔ active s) (fixed : ∀ s, ¬ active s → σ s = s)
    (φ : PolMul.Spectral ℂ) (t : Fin 3 → ℝ) (ht : ∀ i, theta φ i ≤ t i)
    (hs : t 0 + t 1 + t 2 = (9 : ℝ) / 4) (T : Tensor ℂ (X x) (X y) Z) :
    value φ (Network.contract (C := C) T (permutationBond σ) (Network.identity _) (Network.identity _)) ≤
      (2 : ℝ) ^ ((Fintype.card A + Fintype.card B : ℕ) *
        (t 1 * x + t 0 * y) +
        (2 * t 2 - (9 : ℝ) / 4) * Fintype.card (EqualSlots σ active)) * value φ T ^ Fintype.card C := by
  rw [value_retainedAB]
  exact mul_le_mul_of_nonneg_right
    (value_le_change_fintypes φ _ (pair_star_enlarged σ active stable fixed φ t ht hs T))
    (pow_nonneg (φ.nonneg _) _)

end ExtractionAB
end OM.NNN11
