import Lib.OM.NNN11.PermutationNetwork
import Lib.OM.NNN11.MixedCrossings

/-! Coordinate-level versions of the actual rectangular bond reindexings.
They identify every selected equality with a literal passive output bit. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN11.BondCoordinates
open Network SlotExtraction ExtractionAB Wiring
set_option maxHeartbeats 1500000

variable {A B : Type} {b x y L : ℕ}
  (e : (A ⊕ B) ≃ Fin b × ZMod 7) (hx : L ≤ x) (hy : L ≤ y)

abbrev High (A B : Type) (x y L : ℕ) := (A × Fin (y - L)) ⊕ (B × Fin (x - L))

def forward : Slot A B x y → (Fin (b * L) × ZMod 7) ⊕ High A B x y L
  | .inl (a, d) =>
    if h : d.val < L then
      .inl (finProdFinEquiv ((e (.inl a)).1, ⟨d.val, h⟩), (e (.inl a)).2)
    else .inr (.inl (a, ⟨d.val - L, by omega⟩))
  | .inr (a, d) =>
    if h : d.val < L then
      .inl (finProdFinEquiv ((e (.inr a)).1, ⟨d.val, h⟩), (e (.inr a)).2)
    else .inr (.inr (a, ⟨d.val - L, by omega⟩))

def backward : (Fin (b * L) × ZMod 7) ⊕ High A B x y L → Slot A B x y
  | .inl (i, j) =>
    match e.symm ((finProdFinEquiv.symm i).1, j) with
    | .inl a => .inl (a, ⟨(finProdFinEquiv.symm i).2.val,
        lt_of_lt_of_le (finProdFinEquiv.symm i).2.isLt hy⟩)
    | .inr a => .inr (a, ⟨(finProdFinEquiv.symm i).2.val,
        lt_of_lt_of_le (finProdFinEquiv.symm i).2.isLt hx⟩)
  | .inr (.inl (a, d)) => .inl (a, ⟨L + d.val, by omega⟩)
  | .inr (.inr (a, d)) => .inr (a, ⟨L + d.val, by omega⟩)

lemma backward_forward (s : Slot A B x y) : backward e hx hy (forward e hx hy s) = s := by
  rcases s with ⟨a, d⟩ | ⟨a, d⟩
  · by_cases h : d.val < L
    · simp [forward, h, backward]
    · simp only [forward, dif_neg h, backward]
      congr 2
      apply Fin.ext
      dsimp
      omega
  · by_cases h : d.val < L
    · simp [forward, h, backward]
    · simp only [forward, dif_neg h, backward]
      congr 2
      apply Fin.ext
      dsimp
      omega

lemma forward_backward (s : (Fin (b * L) × ZMod 7) ⊕ High A B x y L) :
    forward e hx hy (backward e hx hy s) = s := by
  rcases s with ⟨i, j⟩ | (⟨a, d⟩ | ⟨a, d⟩)
  · obtain ⟨⟨t, d⟩, rfl⟩ := finProdFinEquiv.surjective i
    simp only [backward, Equiv.symm_apply_apply]
    cases he : e.symm (t, j) with
    | inl a =>
      have ha : e (.inl a) = (t, j) := by simpa using! (congrArg e he).symm
      simp [forward, d.isLt, ha]
    | inr a =>
      have ha : e (.inr a) = (t, j) := by simpa using! (congrArg e he).symm
      simp [forward, d.isLt, ha]
  · simp only [backward, forward, dif_neg (by omega : ¬ L + d.val < L)]
    congr 3
    apply Fin.ext
    simp
  · simp only [backward, forward, dif_neg (by omega : ¬ L + d.val < L)]
    congr 3
    apply Fin.ext
    simp

def layout : Slot A B x y ≃ (Fin (b * L) × ZMod 7) ⊕ High A B x y L where
  toFun := forward e hx hy
  invFun := backward e hx hy
  left_inv := backward_forward e hx hy
  right_inv := forward_backward e hx hy

lemma layout_role (p : Fin (b * L) × ZMod 7) :
    slotRole ((layout e hx hy).symm (.inl p)) ↔
      slotRole (e.symm ((finProdFinEquiv.symm p.1).1, p.2)) := by
  dsimp [layout, backward]
  split <;> simp_all [slotRole]

lemma heavy_inverse_role (p : Fin 7 × ZMod 7) :
    slotRole (Tiles.heavyTiles.symm p) ↔ p.2 ∈ fano := by
  obtain ⟨s, rfl⟩ := Tiles.heavyTiles.surjective p
  cases s with
  | inl a => simp [slotRole, Tiles.heavy_left_role a]
  | inr a => simp [slotRole, Tiles.heavy_right_role a]

lemma light_inverse_role (p : Fin 6 × ZMod 7) :
    slotRole (Tiles.lightTiles.symm p) ↔ Tiles.lightRole p := by
  obtain ⟨s, rfl⟩ := Tiles.lightTiles.surjective p
  cases s with
  | inl a => simp [slotRole, Tiles.light_left_role a]
  | inr a => simp [slotRole, Tiles.light_right_role a]

def heavyLayout (x y : ℕ) :=
  layout Tiles.heavyTiles (min_le_left x y) (min_le_right x y)

def lightLayout (x y : ℕ) :=
  layout Tiles.lightTiles (min_le_left x y) (min_le_right x y)

def reverseHeavyTiles : (Fin 28 ⊕ Fin 21) ≃ Fin 7 × ZMod 7 :=
  (Equiv.sumComm _ _).trans Tiles.heavyTiles

lemma reverse_heavy_inverse_role (p : Fin 7 × ZMod 7) :
    slotRole (reverseHeavyTiles.symm p) ↔ p.2 ∉ fano := by
  have h := heavy_inverse_role p
  dsimp [reverseHeavyTiles]
  cases he : Tiles.heavyTiles.symm p <;> simpa [he, slotRole] using! not_congr h

def reverseHeavyLayout (x y : ℕ) :=
  layout reverseHeavyTiles (min_le_left x y) (min_le_right x y)

theorem heavy_selected_card (x y : ℕ) (c : Word (7 * min x y)) :
    Fintype.card (EqualSlots (MixedCrossings.permutation (heavyLayout x y) c)
      (MixedCrossings.active (heavyLayout x y) c)) = 2 * weight c := by
  apply MixedCrossings.transported_selected_card (heavyLayout x y) (fun _ => false) c slotRole
  intro p
  rw [show heavyLayout x y = layout Tiles.heavyTiles (min_le_left x y) (min_le_right x y) from rfl,
    layout_role, heavy_inverse_role]
  rfl

theorem light_selected_card (x y : ℕ) (c : Word (6 * min x y)) :
    Fintype.card (EqualSlots (MixedCrossings.permutation (lightLayout x y) c)
      (MixedCrossings.active (lightLayout x y) c)) = 2 * weight c := by
  apply MixedCrossings.transported_selected_card (lightLayout x y)
    (fun i => if (finProdFinEquiv.symm i : Fin 6 × Fin (min x y)).1.val < 3
      then false else true) c slotRole
  intro p
  rw [show lightLayout x y = layout Tiles.lightTiles (min_le_left x y) (min_le_right x y) from rfl,
    layout_role, light_inverse_role]
  simp only [Tiles.lightRole, MixedCrossings.tileRole, MixedCrossings.role]
  split_ifs <;> simp_all

theorem reverse_heavy_selected_card (x y : ℕ) (c : Word (7 * min x y)) :
    Fintype.card (EqualSlots (MixedCrossings.permutation (reverseHeavyLayout x y) c)
      (MixedCrossings.active (reverseHeavyLayout x y) c)) = 2 * weight c := by
  apply MixedCrossings.transported_selected_card (reverseHeavyLayout x y) (fun _ => true) c slotRole
  intro p
  rw [show reverseHeavyLayout x y = layout reverseHeavyTiles
      (min_le_left x y) (min_le_right x y) from rfl,
    layout_role, reverse_heavy_inverse_role]
  rfl

end OM.NNN11.BondCoordinates
