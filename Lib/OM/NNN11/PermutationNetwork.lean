import Lib.OM.NNN11.ExtractionDimensions
import Lib.OM.NNN11.EdgeFactor

/-! Connect partial-permutation extraction to the original physical-bond
contraction, retaining identities on every unacted digit of the selected bond. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN11.Wiring
set_option maxHeartbeats 1000000

variable {S E : Type} (σ : S ≃ S) (active : S → Prop)

lemma whole_relation_iff (fixed : ∀ s, ¬ active s → σ s = s) (r c : S → E) :
    Relation σ (fun _ => True) r c ↔
      Relation σ active r c ∧ complement active r = complement active c := by
  constructor
  · intro h
    refine ⟨fun s _ => h s trivial, ?_⟩
    funext s
    simpa [complement, fixed s.1 s.2] using! h s.1 trivial
  · rintro ⟨h, hc⟩ s _
    by_cases hs : active s
    · exact h s hs
    · rw [fixed s hs]
      exact congrFun hc ⟨s, hs⟩

theorem whole_delta_eq_joint (fixed : ∀ s, ¬ active s → σ s = s) (r c : S → E) :
    delta σ (fun _ => True) r c =
      joint σ active (fun u v => if u = v then 1 else 0) r c := by
  unfold delta joint
  rw [whole_relation_iff σ active fixed]
  unfold delta
  split_ifs <;> simp_all

end OM.NNN11.Wiring

namespace OM.NNN11.ExtractionAB
open CoordinateTensor OM.NNN.Raw OM.NNN2 Network SlotExtraction Wiring
set_option maxHeartbeats 1000000

variable {A B C Z : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype Z] {x y : ℕ}

def bitBasis (A B : Type) (x y : ℕ) :
    BondAB A B (X x) (X y) ≃ (Slot A B x y → ZMod 2) :=
  (Equiv.prodCongr (Equiv.curry A (Fin y) (ZMod 2)).symm
    (Equiv.curry B (Fin x) (ZMod 2)).symm).trans
    (Equiv.sumArrowEquivProdArrow (A × Fin y) (B × Fin x) (ZMod 2)).symm

lemma bitBasis_apply (w : BondAB A B (X x) (X y)) :
    bitBasis A B x y w = Sum.elim (Function.uncurry w.1) (Function.uncurry w.2) := rfl

def permutationBond (σ : Slot A B x y ≃ Slot A B x y) : Operator (BondAB A B (X x) (X y)) :=
  fun u v => delta σ (fun _ => True) (bitBasis A B x y u) (bitBasis A B x y v)

lemma permutationBond_refl : permutationBond (A := A) (B := B) (x := x) (y := y)
    (Equiv.refl _) = Network.identity _ := by
  funext u v
  have he : Relation (Equiv.refl (Slot A B x y)) (fun _ => True)
      (bitBasis A B x y u) (bitBasis A B x y v) ↔ u = v := by
    simp only [Relation, Equiv.refl_apply, forall_const, ← funext_iff,
      (bitBasis A B x y).injective.eq_iff]
  simp only [permutationBond, delta, he, Network.identity]
  split_ifs <;> rfl

variable (σ : Slot A B x y ≃ Slot A B x y) (active : Slot A B x y → Prop)

def productComplement (Q : Operator (BondBC B C (X y) Z))
    (R : Operator (BondCA C A Z (X x))) : JointComplement (C := C) (Z := Z) active :=
  fun u v b b' c c' => (if u = v then 1 else 0) * Q b b' * R c c'

theorem contract_eq_joint (fixed : ∀ s, ¬ active s → σ s = s)
    (T : Tensor ℂ (X x) (X y) Z) (Q : Operator (BondBC B C (X y) Z))
    (R : Operator (BondCA C A Z (X x))) :
    Network.contract T (permutationBond σ) Q R =
      jointContract σ active T (productComplement active Q R) := by
  funext xx yy zz
  unfold Network.contract jointContract
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  unfold permutationBond
  rw [whole_delta_eq_joint σ active fixed]
  simp only [joint, productComplement, bitBasis_apply]
  split_ifs <;> ring

theorem permutation_network_restriction (stable : ∀ s, active (σ s) ↔ active s)
    (fixed : ∀ s, ¬ active s → σ s = s)
    (T : Tensor ℂ (X x) (X y) Z) (Q : Operator (BondBC B C (X y) Z))
    (R : Operator (BondCA C A Z (X x))) :
    Restricts (mm (ResidualX (C := C) σ active) (ResidualY (C := C) σ active)
      (EqualSlots σ active → ZMod 2)) (Network.contract T (permutationBond σ) Q R) := by
  rw [contract_eq_joint σ active fixed]
  exact jointContract_restriction σ active stable T _

theorem permutation_network_edge_value [Nonempty Z]
    (stable : ∀ s, active (σ s) ↔ active s) (fixed : ∀ s, ¬ active s → σ s = s)
    (φ : PolMul.Spectral ℂ) (T : Tensor ℂ (X x) (X y) Z)
    (Q : Operator (BondBC B C (X y) Z)) (R : Operator (BondCA C A Z (X x))) :
    value φ (Network.contract T (permutationBond σ) Q R) ≤
      value φ (residual σ active T (productComplement active Q R)) *
        (Fintype.card (EqualSlots σ active → ZMod 2) : ℝ) ^ Foundations.PairUnitExponents.theta φ 2 := by
  rw [contract_eq_joint σ active fixed]
  exact residual_edge_value σ active stable φ T _

end OM.NNN11.ExtractionAB
