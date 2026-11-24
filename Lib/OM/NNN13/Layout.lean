import Lib.OM.NNN13.Packing
import Lib.OM.NNN12.Layout

noncomputable section
open scoped BigOperators Classical
namespace OM.NNN13
open NNN11.SlotExtraction NNN11.ExtractionAB NNN12
set_option maxHeartbeats 1000000

namespace AllPositions

private lemma card_false (I : Type) [Fintype I] {h : Fintype {_i : I // False}} :
    Fintype.card {_i : I // False} = 0 :=
  Fintype.card_eq_zero_iff.mpr ⟨fun i => i.property⟩

def roleEquiv {I J P : Type} [Fintype I] [Fintype J] [Fintype P]
    (r : P → Prop) (hI : Fintype.card I = Fintype.card {p // r p})
    (hJ : Fintype.card J = Fintype.card {p // ¬ r p}) : (I ⊕ J) ≃ P :=
  (Equiv.sumCongr (Fintype.equivOfCardEq hI) (Fintype.equivOfCardEq hJ)).trans
    (Equiv.sumCompl r)

lemma roleEquiv_role {I J P : Type} [Fintype I] [Fintype J] [Fintype P]
    (r : P → Prop) (hI : Fintype.card I = Fintype.card {p // r p})
    (hJ : Fintype.card J = Fintype.card {p // ¬ r p}) (p : P) :
    slotRole ((roleEquiv r hI hJ).symm p) ↔ r p := by
  apply Tiles.inverse_role
  · intro i
    exact (Fintype.equivOfCardEq hI i).property
  · intro j
    exact (Fintype.equivOfCardEq hJ j).property

/-- Enough positions of each role suffice for a layout, with no condition on
which copies or digit levels supply them. -/
theorem exists_coordinates {I J P : Type} [Fintype I] [Fintype J] [Fintype P]
    (r : P → Prop) (hI : Fintype.card {p // r p} ≤ Fintype.card I)
    (hJ : Fintype.card {p // ¬ r p} ≤ Fintype.card J) :
    ∃ e : (I ⊕ J) ≃ P ⊕
        (Fin (Fintype.card I - Fintype.card {p // r p}) ⊕
         Fin (Fintype.card J - Fintype.card {p // ¬ r p})),
      ∀ p, slotRole (e.symm (.inl p)) ↔ r p := by
  let H := Fin (Fintype.card I - Fintype.card {p // r p}) ⊕
    Fin (Fintype.card J - Fintype.card {p // ¬ r p})
  let R : P ⊕ H → Prop := Sum.elim r slotRole
  have hpos : Fintype.card {s // R s} = Fintype.card I := by
    rw [Fintype.card_congr Equiv.subtypeSum, Fintype.card_sum]
    change Fintype.card {p // r p} + Fintype.card {h : H // slotRole h} = _
    rw [Fintype.card_congr Equiv.subtypeSum, Fintype.card_sum]
    simp only [slotRole, Fintype.card_subtype_true, card_false,
      Fintype.card_fin, add_zero]
    omega
  have hneg : Fintype.card {s // ¬ R s} = Fintype.card J := by
    rw [Fintype.card_congr Equiv.subtypeSum, Fintype.card_sum]
    change Fintype.card {p // ¬ r p} + Fintype.card {h : H // ¬ slotRole h} = _
    rw [Fintype.card_congr Equiv.subtypeSum, Fintype.card_sum]
    simp only [slotRole, not_true_eq_false, not_false_eq_true,
      Fintype.card_subtype_true, card_false, Fintype.card_fin, zero_add]
    omega
  exact ⟨roleEquiv R hpos.symm hneg.symm,
    fun p => roleEquiv_role R hpos.symm hneg.symm (.inl p)⟩

def layoutOfCounts {q d N x y : ℕ} [Fact q.Prime]
    {A B : Type} [Fintype A] [Fintype B]
    (D : Finset (ZMod q)) (hD : Cyclic.ShiftCounts D d) (flip : Fin N → Bool)
    (hA : Fintype.card {p // Cyclic.tileRole D flip p} ≤ Fintype.card A * y)
    (hB : Fintype.card {p // ¬ Cyclic.tileRole D flip p} ≤ Fintype.card B * x) :
    BondLayout q d A B x y N where
  High := Fin (Fintype.card (A × Fin y) - Fintype.card {p // Cyclic.tileRole D flip p}) ⊕
    Fin (Fintype.card (B × Fin x) - Fintype.card {p // ¬ Cyclic.tileRole D flip p})
  finiteHigh := inferInstance
  coordinates := Classical.choose (exists_coordinates (I := A × Fin y) (J := B × Fin x)
    (Cyclic.tileRole D flip) (by simpa using! hA) (by simpa using! hB))
  crossings c := by
    apply Cyclic.transported_selected_card _ D hD flip c slotRole
    exact Classical.choose_spec (exists_coordinates (I := A × Fin y) (J := B × Fin x)
      (Cyclic.tileRole D flip) (by simpa using! hA) (by simpa using! hB))

def mixedFlip (u v : ℕ) (i : Fin (u + v)) : Bool :=
  Sum.elim (fun _ => false) (fun _ => true) (finSumFinEquiv.symm i)

lemma role_card {q : ℕ} [Fact q.Prime] (D : Finset (ZMod q)) (b : Bool) :
    Fintype.card {j // Cyclic.role D b j} = if b then q - D.card else D.card := by
  cases b
  · simp [Cyclic.role]
  · simp [Cyclic.role, Fintype.card_subtype_compl]

lemma mixed_role_card {q : ℕ} [Fact q.Prime] (D : Finset (ZMod q)) (u v : ℕ) :
    Fintype.card {p // Cyclic.tileRole D (mixedFlip u v) p} =
      u * D.card + v * (q - D.card) := by
  change Fintype.card {p : Fin (u + v) × ZMod q //
    Cyclic.role D (mixedFlip u v p.1) p.2} = _
  rw [Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype
    (fun i j => Cyclic.role D (mixedFlip u v i) j)), Fintype.card_sigma]
  simp_rw [role_card]
  rw [← Equiv.sum_comp finSumFinEquiv]
  simp [mixedFlip, Fintype.sum_sum_type]

lemma mixed_nonrole_card {q : ℕ} [Fact q.Prime] (D : Finset (ZMod q)) (u v : ℕ) :
    Fintype.card {p // ¬ Cyclic.tileRole D (mixedFlip u v) p} =
      u * (q - D.card) + v * D.card := by
  have hD : D.card ≤ q := by simpa using! D.card_le_univ
  rw [Fintype.card_subtype_compl, mixed_role_card]
  simp only [Fintype.card_prod, Fintype.card_fin, ZMod.card]
  have he : (u + v) * q = (u * D.card + v * (q - D.card)) +
      (u * (q - D.card) + v * D.card) := by
    have hh : q = D.card + (q - D.card) := (Nat.add_sub_of_le hD).symm
    conv_lhs => rw [hh]
    ring
  omega

/-- Mixed orientations use precisely `k*u+(k+1)*v` positions of the first
role and `(k+1)*u+k*v` of the second. -/
def mixedLayout {q k d x y u v : ℕ} [Fact q.Prime]
    {A B : Type} [Fintype A] [Fintype B]
    (D : Finset (ZMod q)) (hq : q = 2 * k + 1) (hcard : D.card = k)
    (hD : Cyclic.ShiftCounts D d)
    (hA : k * u + (k + 1) * v ≤ Fintype.card A * y)
    (hB : (k + 1) * u + k * v ≤ Fintype.card B * x) :
    BondLayout q d A B x y (u + v) :=
  layoutOfCounts D hD (mixedFlip u v)
    (by
      rw [mixed_role_card, hcard, hq, show 2 * k + 1 - k = k + 1 by omega]
      simpa only [Nat.mul_comm] using! hA)
    (by
      rw [mixed_nonrole_card, hcard, hq, show 2 * k + 1 - k = k + 1 by omega]
      simpa only [Nat.mul_comm] using! hB)

/-- The fractional optimum is realized on the physical bond with a loss
strictly below two cycles, uniformly in all dimensions and owner counts. -/
theorem exists_packed_layout {q k d x y : ℕ} [Fact q.Prime]
    {A B : Type} [Fintype A] [Fintype B]
    (D : Finset (ZMod q)) (hq : q = 2 * k + 1) (hk : 0 < k)
    (hcard : D.card = k) (hD : Cyclic.ShiftCounts D d) :
    ∃ N : ℕ, Nonempty (BondLayout q d A B x y N) ∧
      (N : ℝ) ≤ capacity k (Fintype.card A * y) (Fintype.card B * x) ∧
      capacity k (Fintype.card A * y) (Fintype.card B * x) < (N : ℝ) + 2 := by
  obtain ⟨u, v, hA, hB, hlo, hhi⟩ :=
    packing_integer (A := Fintype.card A * y) (B := Fintype.card B * x) hk
  refine ⟨u + v, ⟨mixedLayout D hq hcard hD hA hB⟩, ?_, ?_⟩
  · simpa only [Nat.cast_add, Nat.cast_mul] using! hlo
  · simpa only [Nat.cast_add, Nat.cast_mul] using! hhi

end AllPositions
end OM.NNN13
