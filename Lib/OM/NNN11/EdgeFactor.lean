import Lib.OM.NNN11.Extraction

/-! The extracted residual retains its actual spectral value at the same point. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN11
open CoordinateTensor OM.NNN.Raw OM.NNN2 OM.NNN3
set_option maxHeartbeats 1000000

def edgeFactor {R Q Z E : Type} (W : Tensor ℂ R Q Z) : Tensor ℂ (R × E) (Q × E) Z :=
  fun x y z => if x.2 = y.2 then W x.1 y.1 z else 0

theorem value_edgeFactor {R Q Z E : Type} [Fintype R] [Fintype Q] [Fintype Z] [Fintype E]
    [Nonempty R] [Nonempty Q] [Nonempty Z] [Nonempty E]
    (φ : PolMul.Spectral ℂ) (W : Tensor ℂ R Q Z) :
    value φ (edgeFactor (E := E) W) =
      value φ W * (Fintype.card E : ℝ) ^ Foundations.PairUnitExponents.theta φ 2 := by
  have h := value_reindex φ (tensorProduct W (pair E))
    (Equiv.refl _) (Equiv.refl _) (prodUnit Z)
  simp only [Equiv.refl_apply] at h
  have he : (fun x y z => tensorProduct W (pair E) x y (prodUnit Z z)) = edgeFactor W := by
    funext x y z
    simp [tensorProduct, pair, prodUnit, unitProd, edgeFactor]
  rw [he, value_product', value_pair] at h
  exact h

theorem restricts_by_coordinates {R Q Z A B C : Type} [Fintype R] [Fintype Q] [Fintype Z]
    (W : Tensor ℂ R Q Z) (rx : A → R) (ry : B → Q) (rz : C → Z) :
    Restricts W (fun x y z => W (rx x) (ry y) (rz z)) := by
  refine ⟨(fun x => identityRows _ (rx x)), (fun y => identityRows _ (ry y)),
    (fun z => identityRows _ (rz z)), ?_⟩
  funext x y z
  simp [mapTensor, identityRows, ite_mul, mul_ite, Finset.sum_ite_irrel]

namespace ExtractionAB
open Network SlotExtraction Wiring
variable {A B C Z : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype Z] {x y : ℕ}
  (σ : Slot A B x y ≃ Slot A B x y) (active : Slot A B x y → Prop)

theorem residual_edge_restriction (stable : ∀ s, active (σ s) ↔ active s)
    (T : Tensor ℂ (X x) (X y) Z) (K : JointComplement (C := C) (Z := Z) active) :
    Restricts (edgeFactor (E := EqualSlots σ active → ZMod 2) (residual σ active T K))
      (jointContract σ active T K) := by
  rw [residual_factorization σ active stable]
  convert! restricts_by_coordinates
    (edgeFactor (E := EqualSlots σ active → ZMod 2) (residual σ active T K))
    (fun xx => (reduceX σ active xx, outEqualX σ active xx))
    (fun yy => (reduceY σ active yy, outEqualY σ active yy)) id using 1
  funext xx yy zz
  simp only [edgeFactor, id_eq]

theorem residual_edge_value [Nonempty Z] (stable : ∀ s, active (σ s) ↔ active s)
    (φ : PolMul.Spectral ℂ) (T : Tensor ℂ (X x) (X y) Z)
    (K : JointComplement (C := C) (Z := Z) active) :
    value φ (jointContract σ active T K) ≤ value φ (residual σ active T K) *
      (Fintype.card (EqualSlots σ active → ZMod 2) : ℝ) ^ Foundations.PairUnitExponents.theta φ 2 := by
  have h := value_mono φ (restricts_degenerates _ _ (residual_edge_restriction σ active stable T K))
  rw [value_edgeFactor] at h
  exact h

end ExtractionAB
end OM.NNN11
