import Lib.OM.NNN20.Mix.ExtractAB
import Lib.OM.NNN11.ExtractionCA

/-! # Extraction on bond CA of a mixed network

The CA slots are the `x` digits of the class-`C` copies (index `X` of `TC`) and the `z` digits of
the class-`A` copies (index `Z` of `TA`). As NNN.11's `ExtractionCA`, with one tensor per owner
class: the forced equalities are between parties 2 and 0 (edge exponent `θ₁`), and the residual
has format `(|A| xa + |B| xb + |C| x - E, |A| ya + |B| yb + |C| yc, |A| z + |B| zb + |C| zc - E)`. -/

noncomputable section
open scoped BigOperators Classical
namespace OM.NNN20.Mix.CA
open CoordinateTensor OM.NNN.Raw OM.NNN2 OM.NNN11.Network OM.NNN11.SlotExtraction OM.NNN11.Wiring
open OM.NNN11.ExtractionAB (X Slot Complement bitBasis_apply permutationBond)
set_option maxHeartbeats 1000000

variable {A B C XA YA XB YB ZB YC ZC : Type} [Fintype A] [Fintype B] [Fintype C]
  [Fintype XA] [Fintype YA] [Fintype XB] [Fintype YB] [Fintype ZB] [Fintype YC] [Fintype ZC]
  {z x : ℕ}
variable (σ : Slot C A z x ≃ Slot C A z x) (active : Slot C A z x → Prop)

abbrev JointComplement3 := Complement active → Complement active →
  BondAB A B XB YA → BondAB A B XB YA → BondBC B C YC ZB → BondBC B C YC ZB → ℂ

def jointContract3 (TA : Tensor ℂ XA YA (X z)) (TB : Tensor ℂ XB YB ZB) (TC : Tensor ℂ (X x) YC ZC)
    (K : JointComplement3 (B := B) (XB := XB) (YA := YA) (YC := YC) (ZB := ZB) active) :
    Tensor ℂ ((A → XA) × (B → XB) × (C → X x)) ((A → YA) × (B → YB) × (C → YC))
      ((A → X z) × (B → ZB) × (C → ZC)) :=
  fun xx yy zz =>
    ∑ a : (A → YA) × (A → X z),
    ∑ b : (B → XB) × (B → ZB),
    ∑ c : (C → X x) × (C → YC),
      joint σ active
        (fun r s => K r s (a.1, xx.2.1) (yy.1, b.1) (b.2, yy.2.2) (zz.2.1, c.2))
        (Sum.elim (Function.uncurry c.1) (Function.uncurry zz.1))
        (Sum.elim (Function.uncurry xx.2.2) (Function.uncurry a.2)) *
      ordered TA xx.1 a.1 a.2 * ordered TB b.1 yy.2.1 b.2 * ordered TC c.1 c.2 zz.2.2

def normalZ3 (zz : (A → X z) × (B → ZB) × (C → ZC)) : (A → X z) × (B → ZB) × (C → ZC) :=
  ((fun a d => passiveRow σ active 0 (Function.uncurry zz.1) (a, d)), zz.2.1, zz.2.2)

def normalX3 (xx : (A → XA) × (B → XB) × (C → X x)) : (A → XA) × (B → XB) × (C → X x) :=
  (xx.1, xx.2.1, fun c d => passiveCol σ active 0 (Function.uncurry xx.2.2) (c, d))

def outEqualZ3 (zz : (A → X z) × (B → ZB) × (C → ZC)) : EqualSlots σ active → ZMod 2 :=
  equalRow σ active 0 (Function.uncurry zz.1)

def outEqualX3 (xx : (A → XA) × (B → XB) × (C → X x)) : EqualSlots σ active → ZMod 2 :=
  equalCol σ active 0 (Function.uncurry xx.2.2)

theorem jointContract3_extract (stable : ∀ s, active (σ s) ↔ active s)
    (TA : Tensor ℂ XA YA (X z)) (TB : Tensor ℂ XB YB ZB) (TC : Tensor ℂ (X x) YC ZC)
    (K : JointComplement3 (B := B) (XB := XB) (YA := YA) (YC := YC) (ZB := ZB) active)
    (xx : (A → XA) × (B → XB) × (C → X x)) (yy : (A → YA) × (B → YB) × (C → YC))
    (zz : (A → X z) × (B → ZB) × (C → ZC)) :
    jointContract3 σ active TA TB TC K xx yy zz =
      if outEqualZ3 σ active zz = outEqualX3 σ active xx then
        jointContract3 σ active TA TB TC K (normalX3 σ active xx) yy (normalZ3 σ active zz)
      else 0 := by
  unfold jointContract3
  by_cases h : outEqualZ3 σ active zz = outEqualX3 σ active xx
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

abbrev ResidualZ3 := RowRemaining (E := ZMod 2) σ active × (B → ZB) × (C → ZC)
abbrev ResidualX3 := (A → XA) × (B → XB) × ColRemaining (E := ZMod 2) σ active

def reduceZ3 (zz : (A → X z) × (B → ZB) × (C → ZC)) : ResidualZ3 (B := B) (ZB := ZB) (ZC := ZC) σ active :=
  (rowRest σ active (Function.uncurry zz.1), zz.2.1, zz.2.2)

def reduceX3 (xx : (A → XA) × (B → XB) × (C → X x)) : ResidualX3 (B := B) (XA := XA) (XB := XB) σ active :=
  (xx.1, xx.2.1, colRest σ active (Function.uncurry xx.2.2))

def insertZ3 (zz : ResidualZ3 (B := B) (ZB := ZB) (ZC := ZC) σ active) : (A → X z) × (B → ZB) × (C → ZC) :=
  ((fun a d => fillRow σ active 0 zz.1 (a, d)), zz.2.1, zz.2.2)

def insertX3 (xx : ResidualX3 (B := B) (XA := XA) (XB := XB) σ active) : (A → XA) × (B → XB) × (C → X x) :=
  (xx.1, xx.2.1, fun c d => fillCol σ active 0 xx.2.2 (c, d))

def residual3 (TA : Tensor ℂ XA YA (X z)) (TB : Tensor ℂ XB YB ZB) (TC : Tensor ℂ (X x) YC ZC)
    (K : JointComplement3 (B := B) (XB := XB) (YA := YA) (YC := YC) (ZB := ZB) active) :
    Tensor ℂ (ResidualX3 (B := B) (XA := XA) (XB := XB) σ active) ((A → YA) × (B → YB) × (C → YC))
      (ResidualZ3 (B := B) (ZB := ZB) (ZC := ZC) σ active) :=
  fun xx yy zz =>
    jointContract3 σ active TA TB TC K (insertX3 σ active xx) yy (insertZ3 σ active zz)

theorem residual3_factorization (stable : ∀ s, active (σ s) ↔ active s)
    (TA : Tensor ℂ XA YA (X z)) (TB : Tensor ℂ XB YB ZB) (TC : Tensor ℂ (X x) YC ZC)
    (K : JointComplement3 (B := B) (XB := XB) (YA := YA) (YC := YC) (ZB := ZB) active) :
    jointContract3 σ active TA TB TC K = fun xx yy zz =>
      if outEqualZ3 σ active zz = outEqualX3 σ active xx then
        residual3 σ active TA TB TC K (reduceX3 σ active xx) yy (reduceZ3 σ active zz) else 0 := by
  funext xx yy zz
  rw [jointContract3_extract σ active stable]
  simp only [normalZ3, normalX3, passiveRow_eq_fill, passiveCol_eq_fill,
    residual3, reduceZ3, reduceX3, insertZ3, insertX3]

theorem residual3_edge_restriction (stable : ∀ s, active (σ s) ↔ active s)
    (TA : Tensor ℂ XA YA (X z)) (TB : Tensor ℂ XB YB ZB) (TC : Tensor ℂ (X x) YC ZC)
    (K : JointComplement3 (B := B) (XB := XB) (YA := YA) (YC := YC) (ZB := ZB) active) :
    Restricts (OM.NNN11.edgeFactorCA (E := EqualSlots σ active → ZMod 2)
      (residual3 σ active TA TB TC K)) (jointContract3 σ active TA TB TC K) := by
  rw [residual3_factorization σ active stable]
  convert! OM.NNN11.restricts_by_coordinates
    (OM.NNN11.edgeFactorCA (E := EqualSlots σ active → ZMod 2) (residual3 σ active TA TB TC K))
    (fun xx => (reduceX3 σ active xx, outEqualX3 σ active xx)) id
    (fun zz => (reduceZ3 σ active zz, outEqualZ3 σ active zz)) using 1
  funext xx yy zz
  simp only [OM.NNN11.edgeFactorCA, id_eq]

theorem residual3_edge_value [Nonempty XA] [Nonempty YA] [Nonempty XB] [Nonempty YB]
    [Nonempty ZB] [Nonempty YC] [Nonempty ZC] (stable : ∀ s, active (σ s) ↔ active s)
    (φ : PolMul.Spectral ℂ)
    (TA : Tensor ℂ XA YA (X z)) (TB : Tensor ℂ XB YB ZB) (TC : Tensor ℂ (X x) YC ZC)
    (K : JointComplement3 (B := B) (XB := XB) (YA := YA) (YC := YC) (ZB := ZB) active) :
    value φ (jointContract3 σ active TA TB TC K) ≤ value φ (residual3 σ active TA TB TC K) *
      (Fintype.card (EqualSlots σ active → ZMod 2) : ℝ) ^ Foundations.PairUnitExponents.theta φ 1 := by
  have h := value_mono φ (restricts_degenerates _ _
    (residual3_edge_restriction σ active stable TA TB TC K))
  rw [OM.NNN11.value_edgeFactorCA] at h
  exact h

def productComplement3 (P : Operator (BondAB A B XB YA)) (Q : Operator (BondBC B C YC ZB)) :
    JointComplement3 (B := B) (XB := XB) (YA := YA) (YC := YC) (ZB := ZB) active :=
  fun u v a a' b b' => (if u = v then 1 else 0) * P a a' * Q b b'

theorem contract3_eq_joint (fixed : ∀ s, ¬ active s → σ s = s)
    (TA : Tensor ℂ XA YA (X z)) (TB : Tensor ℂ XB YB ZB) (TC : Tensor ℂ (X x) YC ZC)
    (P : Operator (BondAB A B XB YA)) (Q : Operator (BondBC B C YC ZB)) :
    contract3 TA TB TC P Q (permutationBond σ) =
      jointContract3 σ active TA TB TC (productComplement3 active P Q) := by
  funext xx yy zz
  unfold contract3 jointContract3
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  unfold permutationBond
  rw [whole_delta_eq_joint σ active fixed]
  simp only [joint, productComplement3, bitBasis_apply]
  split_ifs <;> ring

theorem permutation3_edge_value [Nonempty XA] [Nonempty YA] [Nonempty XB] [Nonempty YB]
    [Nonempty ZB] [Nonempty YC] [Nonempty ZC]
    (stable : ∀ s, active (σ s) ↔ active s) (fixed : ∀ s, ¬ active s → σ s = s)
    (φ : PolMul.Spectral ℂ)
    (TA : Tensor ℂ XA YA (X z)) (TB : Tensor ℂ XB YB ZB) (TC : Tensor ℂ (X x) YC ZC)
    (P : Operator (BondAB A B XB YA)) (Q : Operator (BondBC B C YC ZB)) :
    value φ (contract3 TA TB TC P Q (permutationBond σ)) ≤
      value φ (residual3 σ active TA TB TC (productComplement3 active P Q)) *
        (Fintype.card (EqualSlots σ active → ZMod 2) : ℝ) ^ Foundations.PairUnitExponents.theta φ 1 := by
  rw [contract3_eq_joint σ active fixed]
  exact residual3_edge_value σ active stable φ TA TB TC _

theorem residualX3_card {xa xb : ℕ} :
    Fintype.card (ResidualX3 (B := B) (XA := X xa) (XB := X xb) σ active) =
      2 ^ (Fintype.card A * xa + Fintype.card B * xb + Fintype.card C * x -
        Fintype.card (EqualSlots σ active)) := by
  have h := equalSlots_le_col σ active
  simp only [Fintype.card_prod, Fintype.card_fin] at h
  simp only [ResidualX3, ColRemaining, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_subtype_compl, selected_col_card, X, ZMod.card, Fintype.card_fin, ← pow_mul,
    ← pow_add]
  congr 1
  rw [Nat.mul_comm (Fintype.card A) xa, Nat.mul_comm (Fintype.card B) xb]
  omega

theorem residualZ3_card {zb zc : ℕ} :
    Fintype.card (ResidualZ3 (B := B) (ZB := X zb) (ZC := X zc) σ active) =
      2 ^ (Fintype.card A * z + Fintype.card B * zb + Fintype.card C * zc -
        Fintype.card (EqualSlots σ active)) := by
  have h := equalSlots_le_row σ active
  simp only [Fintype.card_prod, Fintype.card_fin] at h
  simp only [ResidualZ3, RowRemaining, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_subtype_compl, selected_row_card, X, ZMod.card, Fintype.card_fin, ← pow_mul,
    ← pow_add]
  congr 1
  rw [Nat.mul_comm (Fintype.card B) zb, Nat.mul_comm (Fintype.card C) zc]
  omega

end OM.NNN20.Mix.CA

namespace OM.NNN20.Mix.CA
open CoordinateTensor OM.NNN.Raw OM.NNN2 OM.NNN11.Network OM.NNN11.SlotExtraction
open OM.NNN11.ExtractionAB (X)
open OM.NNN12.Codes Foundations.PairUnitExponents
set_option maxHeartbeats 2000000

variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C]
  {q k z x N : ℕ} [Fact q.Prime]

/-- **A full CA correction word of a mixed network**. -/
theorem full_CA3 (L : OM.NNN12.BondLayout q k C A z x N) (cw : Word q N)
    (φ : PolMul.Spectral ℂ) {xa ya xb yb zb yc zc : ℕ}
    (TA : Tensor ℂ (X xa) (X ya) (X z)) (TB : Tensor ℂ (X xb) (X yb) (X zb))
    (TC : Tensor ℂ (X x) (X yc) (X zc))
    (P : Operator (BondAB A B (X xb) (X ya))) (Q : Operator (BondBC B C (X yc) (X zb)))
    {G : ℝ}
    (hb : ∀ U : OM.NNN12.DyadicTensor
      ![Fintype.card A * xa + Fintype.card B * xb + Fintype.card C * x - k * weight cw,
        Fintype.card A * ya + Fintype.card B * yb + Fintype.card C * yc,
        Fintype.card A * z + Fintype.card B * zb + Fintype.card C * zc - k * weight cw],
      value φ U ≤ (2 : ℝ) ^ G)
    (t : ℝ) (ht : theta φ 1 ≤ t) :
    value φ (contract3 TA TB TC P Q (L.kernel cw)) ≤ (2 : ℝ) ^ (G + t * (k * weight cw)) := by
  let σ := OM.NNN12.Cyclic.permutation L.coordinates cw
  let active := OM.NNN12.Cyclic.active L.coordinates cw
  let W := residual3 σ active TA TB TC (productComplement3 active P Q)
  have heq : Fintype.card (EqualSlots σ active) = k * weight cw := L.crossings cw
  have hw := AB.bound_of_card_at φ _ hb
    (by
      have hd := residualX3_card (B := B) (xa := xa) (xb := xb) σ active
      rw [heq] at hd
      exact OM.NNN11.card_eq_change_fintypes hd)
    (by
      show Fintype.card ((A → X ya) × (B → X yb) × (C → X yc)) =
        2 ^ (Fintype.card A * ya + Fintype.card B * yb + Fintype.card C * yc)
      simp only [Fintype.card_prod, Fintype.card_fun, X, ZMod.card, Fintype.card_fin, ← pow_mul,
        ← pow_add]
      congr 1
      ring)
    (by
      have hd := residualZ3_card (B := B) (zb := zb) (zc := zc) σ active
      rw [heq] at hd
      exact OM.NNN11.card_eq_change_fintypes hd)
    W
  have he := permutation3_edge_value σ active
    (OM.NNN12.Cyclic.stable L.coordinates cw) (OM.NNN12.Cyclic.fixed L.coordinates cw) φ
    TA TB TC P Q
  simp only [Fintype.card_fun, ZMod.card, heq, Nat.cast_pow, Nat.cast_ofNat] at he
  have hh := OM.NNN12.edge_price (k * weight cw) ht he (OM.NNN11.value_le_change_fintypes φ _ hw)
  simpa only [Nat.cast_mul] using! OM.NNN11.value_le_change_fintypes φ _ hh

end OM.NNN20.Mix.CA
