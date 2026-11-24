import Lib.OM.NNN11.Prices
import Lib.OM.NNN11.ValueInstances

/-! The last group's star is priced at its actual degree after retaining the
intact copies, at the same spectral point as the original tensor. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN11.ExtractionAB
open CoordinateTensor OM.NNN.Raw OM.NNN2 Network SlotExtraction Wiring
open Foundations.PairUnitExponents
set_option maxHeartbeats 1000000

variable {A B C Z : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype Z] {x y : ℕ}

def addEmpty (E : Type) (w : (A → E) × (B → E)) : Outputs A B Empty E :=
  (w.1, w.2, Empty.elim)

theorem pairAB_as_empty_network (T : Tensor ℂ (X x) (X y) Z)
    (P : Operator (BondAB A B (X x) (X y))) :
    (fun xx yy zz => Network.contract (C := Empty) T P (Network.identity _) (Network.identity _)
      (addEmpty _ xx) (addEmpty _ yy) (addEmpty _ zz)) = pairAB T P := by
  funext xx yy zz
  rw [retainedAB]
  simp [addEmpty, ordered]

variable (σ : Slot A B x y ≃ Slot A B x y) (active : Slot A B x y → Prop)

theorem pairAB_star_price (stable : ∀ s, active (σ s) ↔ active s)
    (fixed : ∀ s, ¬ active s → σ s = s)
    (φ : PolMul.Spectral ℂ) (T : Tensor ℂ (X x) (X y) Z) :
    value φ (pairAB T (permutationBond σ)) ≤
      (2 : ℝ) ^ ((Fintype.card A + Fintype.card B : ℕ) *
        (theta φ 1 * x + theta φ 0 * y) +
        (2 * theta φ 2 - (theta φ 0 + theta φ 1 + theta φ 2)) *
          Fintype.card (EqualSlots σ active)) := by
  have hr := restricts_by_coordinates
    (Network.contract (C := Empty) T (permutationBond σ) (Network.identity _) (Network.identity _))
    (addEmpty (A := A) (B := B) _) (addEmpty _) (addEmpty _)
  rw [pairAB_as_empty_network] at hr
  have hp := permutation_network_star_price σ active stable fixed φ T
    (Network.identity (BondBC B Empty (X y) Z)) (Network.identity (BondCA Empty A Z (X x)))
  simp only [Fintype.card_eq_zero, add_zero] at hp
  exact (value_mono φ (restricts_degenerates _ _ hr)).trans hp

theorem retained_star_price [Nonempty Z] [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (stable : ∀ s, active (σ s) ↔ active s) (fixed : ∀ s, ¬ active s → σ s = s)
    (φ : PolMul.Spectral ℂ) (T : Tensor ℂ (X x) (X y) Z) :
    value φ (Network.contract (C := C) T (permutationBond σ) (Network.identity _) (Network.identity _)) ≤
      (2 : ℝ) ^ ((Fintype.card A + Fintype.card B : ℕ) *
        (theta φ 1 * x + theta φ 0 * y) +
        (2 * theta φ 2 - (theta φ 0 + theta φ 1 + theta φ 2)) *
          Fintype.card (EqualSlots σ active)) * value φ T ^ Fintype.card C := by
  rw [value_retainedAB]
  exact mul_le_mul_of_nonneg_right
    (value_le_change_fintypes φ _ (pairAB_star_price σ active stable fixed φ T))
    (pow_nonneg (φ.nonneg _) _)

end OM.NNN11.ExtractionAB
