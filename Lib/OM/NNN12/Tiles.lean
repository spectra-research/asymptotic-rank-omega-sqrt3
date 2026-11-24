import Lib.OM.NNN12.BondCoordinates

/-! Concrete owner-to-slot bijections for the 28-, 112- and 196-copy
networks. Their role claims are finite kernel checks, not existence
assumptions about a difference set or an abstract source. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN12.Tiles
open Cyclic
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

def position3 : Fin 1 ⊕ Fin 2 → ZMod 3 := Sum.elim ![0] ![1, 2]
def position11 : Fin 5 ⊕ Fin 6 → ZMod 11 := Sum.elim ![1, 3, 4, 5, 9] ![0, 2, 6, 7, 8, 10]
def position19 : Fin 9 ⊕ Fin 10 → ZMod 19 :=
  Sum.elim ![1, 4, 5, 6, 7, 9, 11, 16, 17] ![0, 2, 3, 8, 10, 12, 13, 14, 15, 18]

def tile3 : (Fin 1 ⊕ Fin 2) ≃ ZMod 3 := Equiv.ofBijective position3 (by decide +kernel)
def tile11 : (Fin 5 ⊕ Fin 6) ≃ ZMod 11 := Equiv.ofBijective position11 (by decide +kernel)
def tile19 : (Fin 9 ⊕ Fin 10) ≃ ZMod 19 := Equiv.ofBijective position19 (by decide +kernel)

def repeatTile {l r q : ℕ} (e : (Fin l ⊕ Fin r) ≃ ZMod q) (n : ℕ) :
    (Fin (n * l) ⊕ Fin (n * r)) ≃ Fin n × ZMod q :=
  (Equiv.sumCongr finProdFinEquiv.symm finProdFinEquiv.symm).trans
    ((Equiv.prodSumDistrib (Fin n) (Fin l) (Fin r)).symm.trans
      (Equiv.prodCongr (Equiv.refl _) e))

def heavy3 : (Fin 7 ⊕ Fin 14) ≃ Fin 7 × ZMod 3 := repeatTile tile3 7
def heavy11 : (Fin 35 ⊕ Fin 42) ≃ Fin 7 × ZMod 11 := repeatTile tile11 7
def heavy19 : (Fin 63 ⊕ Fin 70) ≃ Fin 7 × ZMod 19 := repeatTile tile19 7

lemma heavy3_left : ∀ i : Fin 7, (heavy3 (.inl i)).2 ∈ d3 := by decide +kernel
lemma heavy3_right : ∀ i : Fin 14, (heavy3 (.inr i)).2 ∉ d3 := by decide +kernel
lemma heavy11_left : ∀ i : Fin 35, (heavy11 (.inl i)).2 ∈ d11 := by decide +kernel
lemma heavy11_right : ∀ i : Fin 42, (heavy11 (.inr i)).2 ∉ d11 := by decide +kernel
lemma heavy19_left : ∀ i : Fin 63, (heavy19 (.inl i)).2 ∈ d19 := by decide +kernel
lemma heavy19_right : ∀ i : Fin 70, (heavy19 (.inr i)).2 ∉ d19 := by decide +kernel

/-- `h` Fano cycles of each orientation use exactly `7*h` slots per owner. -/
def balancedPosition (h : ℕ) : Fin (7 * h) ⊕ Fin (7 * h) → Fin (2 * h) × ZMod 7
  | .inl i =>
    if hi : i.val < 3 * h then
      (⟨i.val / 3, by omega⟩, ![0, 1, 3] ⟨i.val % 3, Nat.mod_lt _ (by omega)⟩)
    else
      (⟨h + (i.val - 3 * h) / 4, by omega⟩,
        ![2, 4, 5, 6] ⟨(i.val - 3 * h) % 4, Nat.mod_lt _ (by omega)⟩)
  | .inr i =>
    if hi : i.val < 4 * h then
      (⟨i.val / 4, by omega⟩, ![2, 4, 5, 6] ⟨i.val % 4, Nat.mod_lt _ (by omega)⟩)
    else
      (⟨h + (i.val - 4 * h) / 3, by omega⟩,
        ![0, 1, 3] ⟨(i.val - 4 * h) % 3, Nat.mod_lt _ (by omega)⟩)

def light28 : (Fin 7 ⊕ Fin 7) ≃ Fin 2 × ZMod 7 :=
  Equiv.ofBijective (balancedPosition 1) (by decide +kernel)
def light112 : (Fin 35 ⊕ Fin 35) ≃ Fin 10 × ZMod 7 :=
  Equiv.ofBijective (balancedPosition 5) (by decide +kernel)
def light196 : (Fin 63 ⊕ Fin 63) ≃ Fin 18 × ZMod 7 :=
  Equiv.ofBijective (balancedPosition 9) (by decide +kernel)

def balancedRole (h : ℕ) (p : Fin (2 * h) × ZMod 7) : Prop :=
  if p.1.val < h then p.2 ∈ NNN11.fano else p.2 ∉ NNN11.fano

lemma light28_roles :
    (∀ i : Fin 7, balancedRole 1 (light28 (.inl i))) ∧
    (∀ i : Fin 7, ¬ balancedRole 1 (light28 (.inr i))) := by
  unfold balancedRole
  decide +kernel
lemma light112_roles :
    (∀ i : Fin 35, balancedRole 5 (light112 (.inl i))) ∧
    (∀ i : Fin 35, ¬ balancedRole 5 (light112 (.inr i))) := by
  unfold balancedRole
  decide +kernel
lemma light196_roles :
    (∀ i : Fin 63, balancedRole 9 (light196 (.inl i))) ∧
    (∀ i : Fin 63, ¬ balancedRole 9 (light196 (.inr i))) := by
  unfold balancedRole
  decide +kernel

/-- Forward role certificates imply the exact role of every inverse slot. -/
lemma inverse_role {A B P : Type} (e : (A ⊕ B) ≃ P) (r : P → Prop)
    (ha : ∀ i, r (e (.inl i))) (hb : ∀ i, ¬ r (e (.inr i))) (p : P) :
    NNN11.SlotExtraction.slotRole (e.symm p) ↔ r p := by
  obtain ⟨s, rfl⟩ := e.surjective p
  cases s with
  | inl i => simp [NNN11.SlotExtraction.slotRole, ha i]
  | inr i => simp [NNN11.SlotExtraction.slotRole, hb i]

end OM.NNN12.Tiles
