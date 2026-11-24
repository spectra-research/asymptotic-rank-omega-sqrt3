import Lib.OM.NNN11.PermutationNetwork
import Lib.OM.NNN11.OrientedEdges

/-! Literal BC extraction with a joint complement on all other coordinates.
The residual and all sources have the original X,Y,Z party order. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN11.ExtractionBC
open CoordinateTensor OM.NNN.Raw OM.NNN2 Network SlotExtraction Wiring
open ExtractionAB (X Slot permutationBond)
set_option maxHeartbeats 1000000

variable {A B C V : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype V] {y z : ℕ}
  (σ : Slot B C y z ≃ Slot B C y z) (active : Slot B C y z → Prop)

abbrev JointComplement := ExtractionAB.Complement active → ExtractionAB.Complement active →
  BondCA C A (X z) V → BondCA C A (X z) V →
  BondAB A B V (X y) → BondAB A B V (X y) → ℂ

def jointContract (T : Tensor ℂ V (X y) (X z)) (K : JointComplement (A := A) (V := V) active) :
    Tensor ℂ (Outputs A B C V) (Outputs A B C (X y)) (Outputs A B C (X z)) :=
  fun xx yy zz =>
    ∑ a : (A → X y) × (A → X z),
    ∑ b : (B → V) × (B → X z),
    ∑ c : (C → V) × (C → X y),
      joint σ active
        (fun r s => K r s (c.1, zz.1) (xx.2.2, a.2) (a.1, xx.2.1) (yy.1, b.1))
        (Sum.elim (Function.uncurry b.2) (Function.uncurry yy.2.2))
        (Sum.elim (Function.uncurry zz.2.1) (Function.uncurry c.2)) *
      ordered T xx.1 a.1 a.2 * ordered T b.1 yy.2.1 b.2 * ordered T c.1 c.2 zz.2.2

def normalY (yy : Outputs A B C (X y)) : Outputs A B C (X y) :=
  (yy.1, yy.2.1, fun c d => passiveRow σ active 0 (Function.uncurry yy.2.2) (c, d))
def normalZ (zz : Outputs A B C (X z)) : Outputs A B C (X z) :=
  (zz.1, (fun b d => passiveCol σ active 0 (Function.uncurry zz.2.1) (b, d)), zz.2.2)
def outEqualY (yy : Outputs A B C (X y)) : EqualSlots σ active → ZMod 2 :=
  equalRow σ active 0 (Function.uncurry yy.2.2)
def outEqualZ (zz : Outputs A B C (X z)) : EqualSlots σ active → ZMod 2 :=
  equalCol σ active 0 (Function.uncurry zz.2.1)

theorem jointContract_extract (stable : ∀ s, active (σ s) ↔ active s)
    (T : Tensor ℂ V (X y) (X z)) (K : JointComplement (A := A) (V := V) active)
    (xx : Outputs A B C V) (yy : Outputs A B C (X y)) (zz : Outputs A B C (X z)) :
    jointContract σ active T K xx yy zz =
      if outEqualY σ active yy = outEqualZ σ active zz then
        jointContract σ active T K xx (normalY σ active yy) (normalZ σ active zz) else 0 := by
  unfold jointContract
  by_cases h : outEqualY σ active yy = outEqualZ σ active zz
  · rw [if_pos h]
    repeat' (apply Finset.sum_congr rfl; intro _ _)
    rw [joint_extract σ active slotRole stable 0]
    rw [if_pos ((equalities_join_iff σ active 0 _ _ _ _).2 h)]
    rw [eraseRow_join, eraseCol_join]
    rfl
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro a _
    apply Finset.sum_eq_zero
    intro b _
    apply Finset.sum_eq_zero
    intro c _
    rw [joint_extract σ active slotRole stable 0]
    rw [if_neg (fun he => h ((equalities_join_iff σ active 0 _ _ _ _).1 he))]
    simp

abbrev ResidualY := (A → X y) × (B → X y) × RowRemaining (E := ZMod 2) σ active
abbrev ResidualZ := (A → X z) × ColRemaining (E := ZMod 2) σ active × (C → X z)
def reduceY (yy : Outputs A B C (X y)) : ResidualY (A := A) σ active :=
  (yy.1, yy.2.1, rowRest σ active (Function.uncurry yy.2.2))
def reduceZ (zz : Outputs A B C (X z)) : ResidualZ (A := A) σ active :=
  (zz.1, colRest σ active (Function.uncurry zz.2.1), zz.2.2)
def insertY (yy : ResidualY (A := A) σ active) : Outputs A B C (X y) :=
  (yy.1, yy.2.1, fun c d => fillRow σ active 0 yy.2.2 (c, d))
def insertZ (zz : ResidualZ (A := A) σ active) : Outputs A B C (X z) :=
  (zz.1, (fun b d => fillCol σ active 0 zz.2.1 (b, d)), zz.2.2)
def residual (T : Tensor ℂ V (X y) (X z)) (K : JointComplement (A := A) (V := V) active) :
    Tensor ℂ (Outputs A B C V) (ResidualY (A := A) σ active) (ResidualZ (A := A) σ active) :=
  fun xx yy zz => jointContract σ active T K xx (insertY σ active yy) (insertZ σ active zz)

theorem residual_factorization (stable : ∀ s, active (σ s) ↔ active s)
    (T : Tensor ℂ V (X y) (X z)) (K : JointComplement (A := A) (V := V) active) :
    jointContract σ active T K = fun xx yy zz =>
      if outEqualY σ active yy = outEqualZ σ active zz then
        residual σ active T K xx (reduceY σ active yy) (reduceZ σ active zz) else 0 := by
  funext xx yy zz
  rw [jointContract_extract σ active stable]
  simp only [normalY, normalZ, passiveRow_eq_fill, passiveCol_eq_fill,
    residual, reduceY, reduceZ, insertY, insertZ]

theorem jointContract_restriction (stable : ∀ s, active (σ s) ↔ active s)
    (T : Tensor ℂ V (X y) (X z)) (K : JointComplement (A := A) (V := V) active) :
    Restricts (mm (ResidualZ (A := A) σ active) (EqualSlots σ active → ZMod 2)
      (ResidualY (A := A) σ active)) (jointContract σ active T K) := by
  rw [residual_factorization σ active stable]
  convert! NNN10.starBC (reduceY σ active) (outEqualY σ active)
    (reduceZ σ active) (outEqualZ σ active) (fun xx zz yy => residual σ active T K xx yy zz) using 1
  funext xx yy zz
  split_ifs <;> rfl

theorem residual_edge_restriction (stable : ∀ s, active (σ s) ↔ active s)
    (T : Tensor ℂ V (X y) (X z)) (K : JointComplement (A := A) (V := V) active) :
    Restricts (edgeFactorBC (E := EqualSlots σ active → ZMod 2) (residual σ active T K))
      (jointContract σ active T K) := by
  rw [residual_factorization σ active stable]
  convert! restricts_by_coordinates
    (edgeFactorBC (E := EqualSlots σ active → ZMod 2) (residual σ active T K)) id
    (fun yy => (reduceY σ active yy, outEqualY σ active yy))
    (fun zz => (reduceZ σ active zz, outEqualZ σ active zz)) using 1
  funext xx yy zz
  simp only [edgeFactorBC, id_eq]

theorem residual_edge_value [Nonempty V] (stable : ∀ s, active (σ s) ↔ active s)
    (φ : PolMul.Spectral ℂ) (T : Tensor ℂ V (X y) (X z))
    (K : JointComplement (A := A) (V := V) active) :
    value φ (jointContract σ active T K) ≤ value φ (residual σ active T K) *
      (Fintype.card (EqualSlots σ active → ZMod 2) : ℝ) ^ Foundations.PairUnitExponents.theta φ 0 := by
  have h := value_mono φ (restricts_degenerates _ _ (residual_edge_restriction σ active stable T K))
  rw [value_edgeFactorBC] at h
  exact h

def productComplement (P : Operator (BondAB A B V (X y)))
    (R : Operator (BondCA C A (X z) V)) : JointComplement (A := A) (V := V) active :=
  fun u v c c' a a' => (if u = v then 1 else 0) * R c c' * P a a'

theorem contract_eq_joint (fixed : ∀ s, ¬ active s → σ s = s)
    (T : Tensor ℂ V (X y) (X z)) (P : Operator (BondAB A B V (X y)))
    (R : Operator (BondCA C A (X z) V)) :
    Network.contract T P (permutationBond σ) R =
      jointContract σ active T (productComplement active P R) := by
  funext xx yy zz
  unfold Network.contract jointContract
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  unfold permutationBond
  rw [whole_delta_eq_joint σ active fixed]
  simp only [joint, productComplement, ExtractionAB.bitBasis_apply]
  split_ifs <;> ring

theorem permutation_network_restriction (stable : ∀ s, active (σ s) ↔ active s)
    (fixed : ∀ s, ¬ active s → σ s = s)
    (T : Tensor ℂ V (X y) (X z)) (P : Operator (BondAB A B V (X y)))
    (R : Operator (BondCA C A (X z) V)) :
    Restricts (mm (ResidualZ (A := A) σ active) (EqualSlots σ active → ZMod 2)
      (ResidualY (A := A) σ active)) (Network.contract T P (permutationBond σ) R) := by
  rw [contract_eq_joint σ active fixed]
  exact jointContract_restriction σ active stable T _

theorem permutation_network_edge_value [Nonempty V]
    (stable : ∀ s, active (σ s) ↔ active s) (fixed : ∀ s, ¬ active s → σ s = s)
    (φ : PolMul.Spectral ℂ) (T : Tensor ℂ V (X y) (X z))
    (P : Operator (BondAB A B V (X y))) (R : Operator (BondCA C A (X z) V)) :
    value φ (Network.contract T P (permutationBond σ) R) ≤
      value φ (residual σ active T (productComplement active P R)) *
        (Fintype.card (EqualSlots σ active → ZMod 2) : ℝ) ^ Foundations.PairUnitExponents.theta φ 0 := by
  rw [contract_eq_joint σ active fixed]
  exact residual_edge_value σ active stable φ T _

end OM.NNN11.ExtractionBC
