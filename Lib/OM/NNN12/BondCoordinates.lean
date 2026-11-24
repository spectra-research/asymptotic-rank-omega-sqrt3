import Lib.OM.NNN12.Cyclic

/-! Prime-alphabet version of NNN11.BondCoordinates' exact low/high-digit
coordinate equivalence. The old module is unchanged. Every unmatched bit
is preserved; only the cyclic slot alphabet is generalized. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN12.BondCoordinates
open NNN11.Network NNN11.SlotExtraction NNN11.ExtractionAB NNN11.Wiring
set_option maxHeartbeats 1500000

variable {q : ℕ} [Fact q.Prime]
  {A B : Type} {b x y L : ℕ}
  (e : (A ⊕ B) ≃ Fin b × ZMod q) (hx : L ≤ x) (hy : L ≤ y)

abbrev High (A B : Type) (x y L : ℕ) := (A × Fin (y - L)) ⊕ (B × Fin (x - L))

def forward : Slot A B x y → (Fin (b * L) × ZMod q) ⊕ High A B x y L
  | .inl (a, d) =>
    if h : d.val < L then
      .inl (finProdFinEquiv ((e (.inl a)).1, ⟨d.val, h⟩), (e (.inl a)).2)
    else .inr (.inl (a, ⟨d.val - L, by omega⟩))
  | .inr (a, d) =>
    if h : d.val < L then
      .inl (finProdFinEquiv ((e (.inr a)).1, ⟨d.val, h⟩), (e (.inr a)).2)
    else .inr (.inr (a, ⟨d.val - L, by omega⟩))

def backward : (Fin (b * L) × ZMod q) ⊕ High A B x y L → Slot A B x y
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

lemma forward_backward (s : (Fin (b * L) × ZMod q) ⊕ High A B x y L) :
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

def layout : Slot A B x y ≃ (Fin (b * L) × ZMod q) ⊕ High A B x y L where
  toFun := forward e hx hy
  invFun := backward e hx hy
  left_inv := backward_forward e hx hy
  right_inv := forward_backward e hx hy

lemma layout_role (p : Fin (b * L) × ZMod q) :
    slotRole ((layout e hx hy).symm (.inl p)) ↔
      slotRole (e.symm ((finProdFinEquiv.symm p.1).1, p.2)) := by
  dsimp [layout, backward]
  split <;> simp_all [slotRole]

end OM.NNN12.BondCoordinates
