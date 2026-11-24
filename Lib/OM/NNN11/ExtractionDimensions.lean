import Lib.OM.NNN11.Extraction

/-! Exact residual dimensions for arbitrary selected output equalities. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN11.SlotExtraction
open Wiring
set_option maxHeartbeats 1000000

variable {I J E : Type} [Fintype I] [Fintype J] [Fintype E]
  (σ : (I ⊕ J) ≃ (I ⊕ J)) (active : I ⊕ J → Prop)

lemma selected_row_card :
    Fintype.card {j : J // Selected σ active slotRole (.inr j)} =
      Fintype.card (EqualSlots σ active) := by
  have h := Fintype.card_congr (Equiv.subtypeSum (p := Selected σ active slotRole))
  have hz : Fintype.card {i : I // Selected σ active slotRole (.inl i)} = 0 := by
    apply Fintype.card_eq_zero_iff.mpr
    exact ⟨fun i => i.2.2.1 trivial⟩
  simpa only [Fintype.card_sum, hz, zero_add] using! h.symm

lemma selected_col_card :
    Fintype.card {i : I // Selected σ active slotRole (σ.symm (.inl i))} =
      Fintype.card (EqualSlots σ active) := by
  let e : EqualSlots σ active ≃ {s // Selected σ active slotRole (σ.symm s)} :=
    σ.subtypeEquiv (by intro s; simp)
  have h := Fintype.card_congr (e.trans Equiv.subtypeSum)
  have hz : Fintype.card {j : J // Selected σ active slotRole (σ.symm (.inr j))} = 0 := by
    apply Fintype.card_eq_zero_iff.mpr
    refine ⟨fun j => ?_⟩
    simpa [slotRole] using! j.2.2.2
  simpa only [Fintype.card_sum, hz, add_zero] using! h.symm

lemma equalSlots_le_row : Fintype.card (EqualSlots σ active) ≤ Fintype.card J := by
  rw [← selected_row_card]
  exact Fintype.card_subtype_le _

lemma equalSlots_le_col : Fintype.card (EqualSlots σ active) ≤ Fintype.card I := by
  rw [← selected_col_card]
  exact Fintype.card_subtype_le _

lemma rowRemaining_card : Fintype.card (RowRemaining (E := E) σ active) =
    Fintype.card E ^ (Fintype.card J - Fintype.card (EqualSlots σ active)) := by
  simp only [RowRemaining, Fintype.card_fun, Fintype.card_subtype_compl, selected_row_card]

lemma colRemaining_card : Fintype.card (ColRemaining (E := E) σ active) =
    Fintype.card E ^ (Fintype.card I - Fintype.card (EqualSlots σ active)) := by
  simp only [ColRemaining, Fintype.card_fun, Fintype.card_subtype_compl, selected_col_card]

end OM.NNN11.SlotExtraction

namespace OM.NNN11.ExtractionAB
open Network SlotExtraction Wiring
variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C] {x y : ℕ}
  (σ : Slot A B x y ≃ Slot A B x y) (active : Slot A B x y → Prop)

theorem residualX_card : Fintype.card (ResidualX (C := C) σ active) =
    2 ^ ((Fintype.card A + Fintype.card B + Fintype.card C) * x -
      Fintype.card (EqualSlots σ active)) := by
  have h := equalSlots_le_row σ active
  simp only [Fintype.card_prod, Fintype.card_fin] at h
  simp only [ResidualX, RowRemaining, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_subtype_compl, selected_row_card,
    X, ZMod.card, Fintype.card_fin, ← pow_mul, ← pow_add]
  congr 1
  simp only [Nat.add_mul, Nat.mul_comm x]
  omega

theorem residualY_card : Fintype.card (ResidualY (C := C) σ active) =
    2 ^ ((Fintype.card A + Fintype.card B + Fintype.card C) * y -
      Fintype.card (EqualSlots σ active)) := by
  have h := equalSlots_le_col σ active
  simp only [Fintype.card_prod, Fintype.card_fin] at h
  simp only [ResidualY, ColRemaining, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_subtype_compl, selected_col_card,
    X, ZMod.card, Fintype.card_fin, ← pow_mul, ← pow_add]
  congr 1
  simp only [Nat.add_mul, Nat.mul_comm y]
  omega

theorem equality_card : Fintype.card (EqualSlots σ active → ZMod 2) =
    2 ^ Fintype.card (EqualSlots σ active) := by
  simp

end OM.NNN11.ExtractionAB
