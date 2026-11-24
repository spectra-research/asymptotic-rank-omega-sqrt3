import Lib.OM.NNN12.Codes

/-! Literal difference sets and cyclic actions for the mixed-alphabet networks.
All finite certificates are reduced by the kernel. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN12.Cyclic
open Codes
set_option maxHeartbeats 2000000

instance three_prime : Fact (Nat.Prime 3) := ⟨by decide +kernel⟩
instance eleven_prime : Fact (Nat.Prime 11) := ⟨by decide +kernel⟩
instance nineteen_prime : Fact (Nat.Prime 19) := ⟨by decide +kernel⟩

def d3 : Finset (ZMod 3) := {0}
def d11 : Finset (ZMod 11) := {1, 3, 4, 5, 9}
def d19 : Finset (ZMod 19) := {1, 4, 5, 6, 7, 9, 11, 16, 17}

def ShiftCounts {q : ℕ} [NeZero q] (D : Finset (ZMod q)) (k : ℕ) : Prop :=
  ∀ g : ZMod q, g ≠ 0 →
    (Finset.univ.filter (fun j => j ∈ D ∧ j + g ∉ D)).card = k ∧
    (Finset.univ.filter (fun j => j ∉ D ∧ j + g ∈ D)).card = k ∧
    (Finset.univ.filter (fun j => j ∈ D ∧ j + g ∈ D)).card = D.card - k

theorem d3_counts : d3.card = 1 ∧ ShiftCounts d3 1 := by
  unfold ShiftCounts
  decide +kernel
theorem d7_counts : NNN11.fano.card = 3 ∧ ShiftCounts NNN11.fano 2 := by
  refine ⟨by decide +kernel, ?_⟩
  intro g hg
  simpa [NNN11.crossings, NNN11.fano] using! NNN11.fano_shift_counts g hg
theorem d11_counts : d11.card = 5 ∧ ShiftCounts d11 3 := by
  unfold ShiftCounts
  decide +kernel
theorem d19_counts : d19.card = 9 ∧ ShiftCounts d19 5 := by
  unfold ShiftCounts
  decide +kernel

variable {q : ℕ} [Fact q.Prime]

def role (D : Finset (ZMod q)) (flip : Bool) (j : ZMod q) : Prop :=
  if flip then j ∉ D else j ∈ D

theorem local_count (D : Finset (ZMod q)) {k : ℕ} (hD : ShiftCounts D k)
    (flip : Bool) (g : ZMod q) :
    (Finset.univ.filter (fun j => g ≠ 0 ∧ ¬ role D flip j ∧ role D flip (j - g))).card =
      if g = 0 then 0 else k := by
  by_cases hg : g = 0
  · simp [hg]
  · obtain ⟨h₁, h₂, _⟩ := hD (-g) (neg_ne_zero.mpr hg)
    cases flip
    · simpa [role, hg, sub_eq_add_neg] using! h₂
    · simpa [role, hg, sub_eq_add_neg] using! h₁

def tilePerm {N : ℕ} (c : Word q N) : (Fin N × ZMod q) ≃ (Fin N × ZMod q) where
  toFun s := (s.1, s.2 - c s.1)
  invFun s := (s.1, s.2 + c s.1)
  left_inv s := by simp
  right_inv s := by simp

def tileActive {N : ℕ} (c : Word q N) (s : Fin N × ZMod q) : Prop := c s.1 ≠ 0
def tileRole {N : ℕ} (D : Finset (ZMod q)) (flip : Fin N → Bool) (s : Fin N × ZMod q) : Prop :=
  role D (flip s.1) s.2

lemma tile_stable {N : ℕ} (c : Word q N) (s : Fin N × ZMod q) :
    tileActive c (tilePerm c s) ↔ tileActive c s := Iff.rfl

lemma tile_fixed {N : ℕ} (c : Word q N) (s : Fin N × ZMod q) (h : ¬ tileActive c s) :
    tilePerm c s = s := by
  have hc : c s.1 = 0 := by simpa [tileActive] using! h
  simp [tilePerm, hc]

theorem selected_card {N k : ℕ} (D : Finset (ZMod q)) (hD : ShiftCounts D k)
    (flip : Fin N → Bool) (c : Word q N) :
    Fintype.card {s // NNN11.Wiring.Selected (tilePerm c) (tileActive c) (tileRole D flip) s} =
      k * weight c := by
  let e : {s // NNN11.Wiring.Selected (tilePerm c) (tileActive c) (tileRole D flip) s} ≃
      (Σ i : Fin N, {j : ZMod q // c i ≠ 0 ∧ ¬ role D (flip i) j ∧ role D (flip i) (j - c i)}) :=
    { toFun := fun s => ⟨s.1.1, ⟨s.1.2, s.2⟩⟩
      invFun := fun s => ⟨(s.1, s.2.1), s.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp_rw [Fintype.card_subtype, local_count D hD]
  simp [weight, Finset.sum_ite, Nat.mul_comm]

section Transport
variable {S H : Type} {N : ℕ} (e : S ≃ (Fin N × ZMod q) ⊕ H)

def permutation (c : Word q N) : S ≃ S :=
  e.trans ((Equiv.sumCongr (tilePerm c) (Equiv.refl H)).trans e.symm)

def active (c : Word q N) (s : S) : Prop :=
  match e s with
  | .inl p => tileActive c p
  | .inr _ => False

lemma stable (c : Word q N) (s : S) : active e c (permutation e c s) ↔ active e c s := by
  simp only [active, permutation, Equiv.trans_apply, Equiv.apply_symm_apply]
  cases e s <;> rfl

lemma fixed (c : Word q N) (s : S) (h : ¬ active e c s) : permutation e c s = s := by
  apply e.injective
  simp only [permutation, Equiv.trans_apply, Equiv.apply_symm_apply]
  cases he : e s with
  | inl p =>
    have hp : ¬ tileActive c p := by simpa [active, he] using! h
    simp [tile_fixed c p hp]
  | inr p => rfl

lemma permutation_zero : permutation e 0 = Equiv.refl S := by
  ext s
  apply e.injective
  simp only [permutation, Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.refl_apply]
  cases e s <;> simp [tilePerm]

lemma permutation_add (c d : Word q N) :
    permutation e (c + d) = (permutation e c).trans (permutation e d) := by
  ext s
  apply e.injective
  simp only [permutation, Equiv.trans_apply, Equiv.apply_symm_apply]
  cases e s <;> simp [tilePerm, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]

/-- The crossing count survives a role-preserving reindexing, with every
unmatched high digit included in the complement. -/
theorem transported_selected_card [Fintype S] [Fintype H]
    (D : Finset (ZMod q)) {k : ℕ} (hD : ShiftCounts D k)
    (flip : Fin N → Bool) (c : Word q N) (r : S → Prop)
    (hr : ∀ p, r (e.symm (.inl p)) ↔ tileRole D flip p) :
    Fintype.card {s // NNN11.Wiring.Selected (permutation e c) (active e c) r s} =
      k * weight c := by
  open NNN11.Wiring in
    let p : (Fin N × ZMod q) ⊕ H → Prop :=
      Sum.elim (Selected (tilePerm c) (tileActive c) (tileRole D flip)) (fun _ => False)
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
    exact selected_card D hD flip c

end Transport

end OM.NNN12.Cyclic
