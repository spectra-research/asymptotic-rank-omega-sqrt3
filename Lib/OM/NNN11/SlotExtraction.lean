import Lib.OM.NNN11.Wiring

/-! Output coordinates of a partial permutation across two ownership classes. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN11.SlotExtraction
open Wiring
set_option maxHeartbeats 1000000

variable {I J E : Type}

def slotRole : I ⊕ J → Prop
  | .inl _ => True
  | .inr _ => False

variable (σ : (I ⊕ J) ≃ (I ⊕ J)) (active : I ⊕ J → Prop) (e : E)

abbrev EqualSlots := {s : I ⊕ J // Selected σ active slotRole s}

def passiveRow (x : J → E) : J → E :=
  fun j => if Selected σ active slotRole (.inr j) then e else x j

def passiveCol (y : I → E) : I → E :=
  fun i => if Selected σ active slotRole (σ.symm (.inl i)) then e else y i

def equalRow (x : J → E) : EqualSlots σ active → E :=
  fun s => Sum.elim (fun _ => e) x s.1

def equalCol (y : I → E) : EqualSlots σ active → E :=
  fun s => Sum.elim y (fun _ => e) (σ s.1)

lemma eraseRow_join (a : I → E) (x : J → E) :
    eraseRow σ active slotRole e (Sum.elim a x) = Sum.elim a (passiveRow σ active e x) := by
  funext s
  cases s with
  | inl i => simp [eraseRow, Selected, slotRole]
  | inr j => rfl

lemma eraseCol_join (y : I → E) (b : J → E) :
    eraseCol σ active slotRole e (Sum.elim y b) = Sum.elim (passiveCol σ active e y) b := by
  funext s
  cases s with
  | inl i => rfl
  | inr j => simp [eraseCol, Selected, slotRole]

lemma equalities_join_iff (a y : I → E) (x b : J → E) :
    Equalities σ active slotRole (Sum.elim a x) (Sum.elim y b) ↔
      equalRow σ active e x = equalCol σ active e y := by
  have hr (s : I ⊕ J) (hs : Selected σ active slotRole s) :
      Sum.elim a x s = Sum.elim (fun _ => e) x s := by
    cases s with
    | inl i => exact False.elim (hs.2.1 trivial)
    | inr j => rfl
  have hc (s : I ⊕ J) (hs : Selected σ active slotRole s) :
      Sum.elim y b (σ s) = Sum.elim y (fun _ => e) (σ s) := by
    cases he : σ s with
    | inl i => rfl
    | inr j => exact False.elim (by simpa [he, slotRole] using! hs.2.2)
  constructor
  · intro h
    funext s
    change Sum.elim (fun _ => e) x s.1 = Sum.elim y (fun _ => e) (σ s.1)
    rw [← hr s.1 s.2, ← hc s.1 s.2]
    exact h s.1 s.2
  · intro h s hs
    rw [hr s hs, hc s hs]
    exact congrFun h ⟨s, hs⟩

abbrev RowRemaining := {j : J // ¬ Selected σ active slotRole (.inr j)} → E
abbrev ColRemaining := {i : I // ¬ Selected σ active slotRole (σ.symm (.inl i))} → E

def rowRest (x : J → E) : RowRemaining (E := E) σ active := fun j => x j.1
def colRest (y : I → E) : ColRemaining (E := E) σ active := fun i => y i.1

def fillRow (x : RowRemaining (E := E) σ active) : J → E :=
  fun j => if h : Selected σ active slotRole (.inr j) then e else x ⟨j, h⟩

def fillCol (y : ColRemaining (E := E) σ active) : I → E :=
  fun i => if h : Selected σ active slotRole (σ.symm (.inl i)) then e else y ⟨i, h⟩

lemma passiveRow_eq_fill (x : J → E) :
    passiveRow σ active e x = fillRow σ active e (rowRest σ active x) := by
  funext j
  simp [passiveRow, fillRow, rowRest]

lemma passiveCol_eq_fill (y : I → E) :
    passiveCol σ active e y = fillCol σ active e (colRest σ active y) := by
  funext i
  simp [passiveCol, fillCol, colRest]

end OM.NNN11.SlotExtraction
