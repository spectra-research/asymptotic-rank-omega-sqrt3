import Lib.OM.NNN11.Wiring

/-! Every tile orientation extracts two bits per nonzero F7 coordinate. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN11.MixedCrossings
open Wiring
set_option maxHeartbeats 1000000

def role (flip : Bool) (j : ZMod 7) : Prop := if flip then j ∉ fano else j ∈ fano

instance roleDecidable (flip : Bool) (j : ZMod 7) : Decidable (role flip j) := by
  unfold role
  infer_instance

lemma local_count : ∀ (flip : Bool) (c : ZMod 7),
    (Finset.univ.filter (fun j : ZMod 7 => c ≠ 0 ∧ ¬ role flip j ∧ role flip (j - c))).card =
      if c = 0 then 0 else 2 := by
  unfold role
  decide +kernel

def tilePerm {N : ℕ} (c : Word N) : (Fin N × ZMod 7) ≃ (Fin N × ZMod 7) where
  toFun s := (s.1, s.2 - c s.1)
  invFun s := (s.1, s.2 + c s.1)
  left_inv s := by simp
  right_inv s := by simp

def tileActive {N : ℕ} (c : Word N) (s : Fin N × ZMod 7) : Prop := c s.1 ≠ 0
def tileRole {N : ℕ} (flip : Fin N → Bool) (s : Fin N × ZMod 7) : Prop := role (flip s.1) s.2

lemma tile_stable {N : ℕ} (c : Word N) (s : Fin N × ZMod 7) :
    tileActive c (tilePerm c s) ↔ tileActive c s := Iff.rfl

lemma tile_fixed {N : ℕ} (c : Word N) (s : Fin N × ZMod 7) (h : ¬ tileActive c s) :
    tilePerm c s = s := by
  have hc : c s.1 = 0 := by simpa [tileActive] using! h
  simp [tilePerm, hc]

theorem selected_card {N : ℕ} (flip : Fin N → Bool) (c : Word N) :
    Fintype.card {s // Selected (tilePerm c) (tileActive c) (tileRole flip) s} =
      2 * weight c := by
  let e : {s // Selected (tilePerm c) (tileActive c) (tileRole flip) s} ≃
      (Σ i : Fin N, {j : ZMod 7 // c i ≠ 0 ∧ ¬ role (flip i) j ∧ role (flip i) (j - c i)}) :=
    { toFun := fun s => ⟨s.1.1, ⟨s.1.2, s.2⟩⟩
      invFun := fun s => ⟨(s.1, s.2.1), s.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp_rw [Fintype.card_subtype, local_count]
  simp [weight, Finset.sum_ite, Nat.mul_comm]

section Transport
variable {S H : Type} {N : ℕ} (e : S ≃ (Fin N × ZMod 7) ⊕ H)

def permutation (c : Word N) : S ≃ S :=
  e.trans ((Equiv.sumCongr (tilePerm c) (Equiv.refl H)).trans e.symm)

def active (c : Word N) (s : S) : Prop :=
  match e s with
  | .inl p => tileActive c p
  | .inr _ => False

lemma stable (c : Word N) (s : S) :
    active e c (permutation e c s) ↔ active e c s := by
  simp only [active, permutation, Equiv.trans_apply, Equiv.apply_symm_apply]
  cases e s <;> rfl

lemma fixed (c : Word N) (s : S) (h : ¬ active e c s) : permutation e c s = s := by
  apply e.injective
  simp only [permutation, Equiv.trans_apply, Equiv.apply_symm_apply]
  cases he : e s with
  | inl p =>
    have hp : ¬ tileActive c p := by simpa [active, he] using! h
    simp [tile_fixed c p hp]
  | inr p => rfl

/-- A role-preserving coordinate reindexing transports the literal crossing
count; unmatched high coordinates contribute no selected equalities. -/
theorem transported_selected_card [Fintype S] [Fintype H]
    (flip : Fin N → Bool) (c : Word N) (r : S → Prop)
    (hr : ∀ p, r (e.symm (.inl p)) ↔ tileRole flip p) :
    Fintype.card {s // Selected (permutation e c) (active e c) r s} = 2 * weight c := by
  let p : (Fin N × ZMod 7) ⊕ H → Prop :=
    Sum.elim (Selected (tilePerm c) (tileActive c) (tileRole flip)) (fun _ => False)
  have heq (s : S) : Selected (permutation e c) (active e c) r s ↔ p (e s) := by
    obtain ⟨t, rfl⟩ := e.symm.surjective s
    cases t with
    | inl q =>
      simp only [Selected, active, permutation, Equiv.trans_apply, Equiv.apply_symm_apply,
        Equiv.sumCongr_apply, Sum.map_inl, hr, p, Sum.elim_inl]
    | inr q => simp [Selected, active, p]
  rw [Fintype.card_congr (e.subtypeEquiv heq), Fintype.card_congr Equiv.subtypeSum,
    Fintype.card_sum]
  have hz : Fintype.card {h : H // p (.inr h)} = 0 := by
    apply Fintype.card_eq_zero_iff.mpr
    exact ⟨fun h => h.2⟩
  rw [hz, add_zero]
  exact selected_card flip c
end Transport

end OM.NNN11.MixedCrossings
