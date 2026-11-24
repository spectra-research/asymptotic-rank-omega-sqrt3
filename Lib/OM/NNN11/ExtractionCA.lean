import Lib.OM.NNN11.PermutationNetwork
import Lib.OM.NNN11.OrientedEdges

/-! Literal CA extraction, with arbitrary joint complementary operators and
the residual in the original party order. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN11.ExtractionCA
open CoordinateTensor OM.NNN.Raw OM.NNN2 Network SlotExtraction Wiring
open ExtractionAB (X Slot permutationBond)
set_option maxHeartbeats 1000000

variable {A B C V : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype V] {z x : ℕ}
  (σ : Slot C A z x ≃ Slot C A z x) (active : Slot C A z x → Prop)

abbrev JointComplement := ExtractionAB.Complement active → ExtractionAB.Complement active →
  BondAB A B (X x) V → BondAB A B (X x) V →
  BondBC B C V (X z) → BondBC B C V (X z) → ℂ

def jointContract (T : Tensor ℂ (X x) V (X z)) (K : JointComplement (B := B) (V := V) active) :
    Tensor ℂ (Outputs A B C (X x)) (Outputs A B C V) (Outputs A B C (X z)) :=
  fun xx yy zz =>
    ∑ a : (A → V) × (A → X z),
    ∑ b : (B → X x) × (B → X z),
    ∑ c : (C → X x) × (C → V),
      joint σ active
        (fun r s => K r s (a.1, xx.2.1) (yy.1, b.1) (b.2, yy.2.2) (zz.2.1, c.2))
        (Sum.elim (Function.uncurry c.1) (Function.uncurry zz.1))
        (Sum.elim (Function.uncurry xx.2.2) (Function.uncurry a.2)) *
      ordered T xx.1 a.1 a.2 * ordered T b.1 yy.2.1 b.2 * ordered T c.1 c.2 zz.2.2

def normalZ (zz : Outputs A B C (X z)) : Outputs A B C (X z) :=
  ((fun a d => passiveRow σ active 0 (Function.uncurry zz.1) (a, d)), zz.2.1, zz.2.2)
def normalX (xx : Outputs A B C (X x)) : Outputs A B C (X x) :=
  (xx.1, xx.2.1, fun c d => passiveCol σ active 0 (Function.uncurry xx.2.2) (c, d))
def outEqualZ (zz : Outputs A B C (X z)) : EqualSlots σ active → ZMod 2 :=
  equalRow σ active 0 (Function.uncurry zz.1)
def outEqualX (xx : Outputs A B C (X x)) : EqualSlots σ active → ZMod 2 :=
  equalCol σ active 0 (Function.uncurry xx.2.2)

theorem jointContract_extract (stable : ∀ s, active (σ s) ↔ active s)
    (T : Tensor ℂ (X x) V (X z)) (K : JointComplement (B := B) (V := V) active)
    (xx : Outputs A B C (X x)) (yy : Outputs A B C V) (zz : Outputs A B C (X z)) :
    jointContract σ active T K xx yy zz =
      if outEqualZ σ active zz = outEqualX σ active xx then
        jointContract σ active T K (normalX σ active xx) yy (normalZ σ active zz) else 0 := by
  unfold jointContract
  by_cases h : outEqualZ σ active zz = outEqualX σ active xx
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

abbrev ResidualZ := RowRemaining (E := ZMod 2) σ active × (B → X z) × (C → X z)
abbrev ResidualX := (A → X x) × (B → X x) × ColRemaining (E := ZMod 2) σ active
def reduceZ (zz : Outputs A B C (X z)) : ResidualZ (B := B) σ active :=
  (rowRest σ active (Function.uncurry zz.1), zz.2.1, zz.2.2)
def reduceX (xx : Outputs A B C (X x)) : ResidualX (B := B) σ active :=
  (xx.1, xx.2.1, colRest σ active (Function.uncurry xx.2.2))
def insertZ (zz : ResidualZ (B := B) σ active) : Outputs A B C (X z) :=
  ((fun a d => fillRow σ active 0 zz.1 (a, d)), zz.2.1, zz.2.2)
def insertX (xx : ResidualX (B := B) σ active) : Outputs A B C (X x) :=
  (xx.1, xx.2.1, fun c d => fillCol σ active 0 xx.2.2 (c, d))
def residual (T : Tensor ℂ (X x) V (X z)) (K : JointComplement (B := B) (V := V) active) :
    Tensor ℂ (ResidualX (B := B) σ active) (Outputs A B C V) (ResidualZ (B := B) σ active) :=
  fun xx yy zz => jointContract σ active T K (insertX σ active xx) yy (insertZ σ active zz)

theorem residual_factorization (stable : ∀ s, active (σ s) ↔ active s)
    (T : Tensor ℂ (X x) V (X z)) (K : JointComplement (B := B) (V := V) active) :
    jointContract σ active T K = fun xx yy zz =>
      if outEqualZ σ active zz = outEqualX σ active xx then
        residual σ active T K (reduceX σ active xx) yy (reduceZ σ active zz) else 0 := by
  funext xx yy zz
  rw [jointContract_extract σ active stable]
  simp only [normalZ, normalX, passiveRow_eq_fill, passiveCol_eq_fill,
    residual, reduceZ, reduceX, insertZ, insertX]

theorem jointContract_restriction (stable : ∀ s, active (σ s) ↔ active s)
    (T : Tensor ℂ (X x) V (X z)) (K : JointComplement (B := B) (V := V) active) :
    Restricts (mm (EqualSlots σ active → ZMod 2) (ResidualZ (B := B) σ active)
      (ResidualX (B := B) σ active)) (jointContract σ active T K) := by
  rw [residual_factorization σ active stable]
  convert! NNN10.starCA (reduceX σ active) (outEqualX σ active)
    (reduceZ σ active) (outEqualZ σ active) (residual σ active T K) using 1
  funext xx yy zz
  simp only [eq_comm]
  split_ifs <;> rfl

theorem residual_edge_restriction (stable : ∀ s, active (σ s) ↔ active s)
    (T : Tensor ℂ (X x) V (X z)) (K : JointComplement (B := B) (V := V) active) :
    Restricts (edgeFactorCA (E := EqualSlots σ active → ZMod 2) (residual σ active T K))
      (jointContract σ active T K) := by
  rw [residual_factorization σ active stable]
  convert! restricts_by_coordinates
    (edgeFactorCA (E := EqualSlots σ active → ZMod 2) (residual σ active T K))
    (fun xx => (reduceX σ active xx, outEqualX σ active xx)) id
    (fun zz => (reduceZ σ active zz, outEqualZ σ active zz)) using 1
  funext xx yy zz
  simp only [edgeFactorCA, id_eq]

theorem residual_edge_value [Nonempty V] (stable : ∀ s, active (σ s) ↔ active s)
    (φ : PolMul.Spectral ℂ) (T : Tensor ℂ (X x) V (X z))
    (K : JointComplement (B := B) (V := V) active) :
    value φ (jointContract σ active T K) ≤ value φ (residual σ active T K) *
      (Fintype.card (EqualSlots σ active → ZMod 2) : ℝ) ^ Foundations.PairUnitExponents.theta φ 1 := by
  have h := value_mono φ (restricts_degenerates _ _ (residual_edge_restriction σ active stable T K))
  rw [value_edgeFactorCA] at h
  exact h

def productComplement (P : Operator (BondAB A B (X x) V))
    (Q : Operator (BondBC B C V (X z))) : JointComplement (B := B) (V := V) active :=
  fun u v a a' b b' => (if u = v then 1 else 0) * P a a' * Q b b'

theorem contract_eq_joint (fixed : ∀ s, ¬ active s → σ s = s)
    (T : Tensor ℂ (X x) V (X z)) (P : Operator (BondAB A B (X x) V))
    (Q : Operator (BondBC B C V (X z))) :
    Network.contract T P Q (permutationBond σ) =
      jointContract σ active T (productComplement active P Q) := by
  funext xx yy zz
  unfold Network.contract jointContract
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  unfold permutationBond
  rw [whole_delta_eq_joint σ active fixed]
  simp only [joint, productComplement, ExtractionAB.bitBasis_apply]
  split_ifs <;> ring

theorem permutation_network_restriction (stable : ∀ s, active (σ s) ↔ active s)
    (fixed : ∀ s, ¬ active s → σ s = s)
    (T : Tensor ℂ (X x) V (X z)) (P : Operator (BondAB A B (X x) V))
    (Q : Operator (BondBC B C V (X z))) :
    Restricts (mm (EqualSlots σ active → ZMod 2) (ResidualZ (B := B) σ active)
      (ResidualX (B := B) σ active)) (Network.contract T P Q (permutationBond σ)) := by
  rw [contract_eq_joint σ active fixed]
  exact jointContract_restriction σ active stable T _

theorem permutation_network_edge_value [Nonempty V]
    (stable : ∀ s, active (σ s) ↔ active s) (fixed : ∀ s, ¬ active s → σ s = s)
    (φ : PolMul.Spectral ℂ) (T : Tensor ℂ (X x) V (X z))
    (P : Operator (BondAB A B (X x) V)) (Q : Operator (BondBC B C V (X z))) :
    value φ (Network.contract T P Q (permutationBond σ)) ≤
      value φ (residual σ active T (productComplement active P Q)) *
        (Fintype.card (EqualSlots σ active → ZMod 2) : ℝ) ^ Foundations.PairUnitExponents.theta φ 1 := by
  rw [contract_eq_joint σ active fixed]
  exact residual_edge_value σ active stable φ T _

end OM.NNN11.ExtractionCA
