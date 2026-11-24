import Lib.OM.NNN20.Mix.Network
import Lib.OM.NNN11.EdgeFactor
import Lib.OM.NNN11.PermutationNetwork
import Lib.OM.NNN11.ExtractionDimensions
import Lib.OM.NNN12.Extraction

/-! # Extraction on bond AB of a mixed network

The AB slots are the `y` digits of the class-`A` copies (index `Y` of `TA`) and the `x` digits of
the class-`B` copies (index `X` of `TB`); the other indices are arbitrary. A partial permutation
of the slots (a code word on a host layout) forces `E` output equalities between parties 0 and 1
and leaves a residual tensor of format `(|A| xa + |B| x + |C| xc - E, |A| y + |B| yb + |C| yc - E,
...)`, with an arbitrary joint operator on the other two bonds. This is NNN.11's
`ExtractionAB` (`jointContract`, `residual_factorization`, `residual_edge_value`,
`residualX_card`) with one tensor per owner class. -/

noncomputable section
open scoped BigOperators Classical
namespace OM.NNN20.Mix.AB
open CoordinateTensor OM.NNN.Raw OM.NNN2 OM.NNN11.Network OM.NNN11.SlotExtraction OM.NNN11.Wiring
open OM.NNN11.ExtractionAB (X Slot Complement bitBasis bitBasis_apply permutationBond)
set_option maxHeartbeats 1000000

variable {A B C XA ZA YB ZB XC YC ZC : Type} [Fintype A] [Fintype B] [Fintype C]
  [Fintype XA] [Fintype ZA] [Fintype YB] [Fintype ZB] [Fintype XC] [Fintype YC] [Fintype ZC]
  {x y : ℕ}
variable (σ : Slot A B x y ≃ Slot A B x y) (active : Slot A B x y → Prop)

/-- an arbitrary joint operator on the unacted AB digits and the other two bonds -/
abbrev JointComplement3 := Complement active → Complement active →
  BondBC B C YC ZB → BondBC B C YC ZB → BondCA C A ZA XC → BondCA C A ZA XC → ℂ

def jointContract3 (TA : Tensor ℂ XA (X y) ZA) (TB : Tensor ℂ (X x) YB ZB) (TC : Tensor ℂ XC YC ZC)
    (K : JointComplement3 (C := C) (YC := YC) (ZB := ZB) (ZA := ZA) (XC := XC) active) :
    Tensor ℂ ((A → XA) × (B → X x) × (C → XC)) ((A → X y) × (B → YB) × (C → YC))
      ((A → ZA) × (B → ZB) × (C → ZC)) :=
  fun xx yy zz =>
    ∑ a : (A → X y) × (A → ZA),
    ∑ b : (B → X x) × (B → ZB),
    ∑ c : (C → XC) × (C → YC),
      joint σ active
        (fun r s => K r s (b.2, yy.2.2) (zz.2.1, c.2) (c.1, zz.1) (xx.2.2, a.2))
        (Sum.elim (Function.uncurry a.1) (Function.uncurry xx.2.1))
        (Sum.elim (Function.uncurry yy.1) (Function.uncurry b.1)) *
      ordered TA xx.1 a.1 a.2 * ordered TB b.1 yy.2.1 b.2 * ordered TC c.1 c.2 zz.2.2

def normalX3 (xx : (A → XA) × (B → X x) × (C → XC)) : (A → XA) × (B → X x) × (C → XC) :=
  (xx.1, (fun b d => passiveRow σ active 0 (Function.uncurry xx.2.1) (b, d)), xx.2.2)

def normalY3 (yy : (A → X y) × (B → YB) × (C → YC)) : (A → X y) × (B → YB) × (C → YC) :=
  ((fun a d => passiveCol σ active 0 (Function.uncurry yy.1) (a, d)), yy.2.1, yy.2.2)

def outEqualX3 (xx : (A → XA) × (B → X x) × (C → XC)) : EqualSlots σ active → ZMod 2 :=
  equalRow σ active 0 (Function.uncurry xx.2.1)

def outEqualY3 (yy : (A → X y) × (B → YB) × (C → YC)) : EqualSlots σ active → ZMod 2 :=
  equalCol σ active 0 (Function.uncurry yy.1)

theorem jointContract3_extract (stable : ∀ s, active (σ s) ↔ active s)
    (TA : Tensor ℂ XA (X y) ZA) (TB : Tensor ℂ (X x) YB ZB) (TC : Tensor ℂ XC YC ZC)
    (K : JointComplement3 (C := C) (YC := YC) (ZB := ZB) (ZA := ZA) (XC := XC) active)
    (xx : (A → XA) × (B → X x) × (C → XC)) (yy : (A → X y) × (B → YB) × (C → YC))
    (zz : (A → ZA) × (B → ZB) × (C → ZC)) :
    jointContract3 σ active TA TB TC K xx yy zz =
      if outEqualX3 σ active xx = outEqualY3 σ active yy then
        jointContract3 σ active TA TB TC K (normalX3 σ active xx) (normalY3 σ active yy) zz
      else 0 := by
  unfold jointContract3
  by_cases h : outEqualX3 σ active xx = outEqualY3 σ active yy
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

abbrev ResidualX3 := (A → XA) × RowRemaining (E := ZMod 2) σ active × (C → XC)
abbrev ResidualY3 := ColRemaining (E := ZMod 2) σ active × (B → YB) × (C → YC)

def reduceX3 (xx : (A → XA) × (B → X x) × (C → XC)) : ResidualX3 (C := C) (XA := XA) (XC := XC) σ active :=
  (xx.1, rowRest σ active (Function.uncurry xx.2.1), xx.2.2)

def reduceY3 (yy : (A → X y) × (B → YB) × (C → YC)) : ResidualY3 (C := C) (YB := YB) (YC := YC) σ active :=
  (colRest σ active (Function.uncurry yy.1), yy.2.1, yy.2.2)

def insertX3 (xx : ResidualX3 (C := C) (XA := XA) (XC := XC) σ active) : (A → XA) × (B → X x) × (C → XC) :=
  (xx.1, (fun b d => fillRow σ active 0 xx.2.1 (b, d)), xx.2.2)

def insertY3 (yy : ResidualY3 (C := C) (YB := YB) (YC := YC) σ active) : (A → X y) × (B → YB) × (C → YC) :=
  ((fun a d => fillCol σ active 0 yy.1 (a, d)), yy.2.1, yy.2.2)

def residual3 (TA : Tensor ℂ XA (X y) ZA) (TB : Tensor ℂ (X x) YB ZB) (TC : Tensor ℂ XC YC ZC)
    (K : JointComplement3 (C := C) (YC := YC) (ZB := ZB) (ZA := ZA) (XC := XC) active) :
    Tensor ℂ (ResidualX3 (C := C) (XA := XA) (XC := XC) σ active) (ResidualY3 (C := C) (YB := YB) (YC := YC) σ active)
      ((A → ZA) × (B → ZB) × (C → ZC)) :=
  fun xx yy zz =>
    jointContract3 σ active TA TB TC K (insertX3 σ active xx) (insertY3 σ active yy) zz

theorem residual3_factorization (stable : ∀ s, active (σ s) ↔ active s)
    (TA : Tensor ℂ XA (X y) ZA) (TB : Tensor ℂ (X x) YB ZB) (TC : Tensor ℂ XC YC ZC)
    (K : JointComplement3 (C := C) (YC := YC) (ZB := ZB) (ZA := ZA) (XC := XC) active) :
    jointContract3 σ active TA TB TC K = fun xx yy zz =>
      if outEqualX3 σ active xx = outEqualY3 σ active yy then
        residual3 σ active TA TB TC K (reduceX3 σ active xx) (reduceY3 σ active yy) zz else 0 := by
  funext xx yy zz
  rw [jointContract3_extract σ active stable]
  simp only [normalX3, normalY3, passiveRow_eq_fill, passiveCol_eq_fill,
    residual3, reduceX3, reduceY3, insertX3, insertY3]

theorem residual3_edge_restriction (stable : ∀ s, active (σ s) ↔ active s)
    (TA : Tensor ℂ XA (X y) ZA) (TB : Tensor ℂ (X x) YB ZB) (TC : Tensor ℂ XC YC ZC)
    (K : JointComplement3 (C := C) (YC := YC) (ZB := ZB) (ZA := ZA) (XC := XC) active) :
    Restricts (OM.NNN11.edgeFactor (E := EqualSlots σ active → ZMod 2)
      (residual3 σ active TA TB TC K)) (jointContract3 σ active TA TB TC K) := by
  rw [residual3_factorization σ active stable]
  convert! OM.NNN11.restricts_by_coordinates
    (OM.NNN11.edgeFactor (E := EqualSlots σ active → ZMod 2) (residual3 σ active TA TB TC K))
    (fun xx => (reduceX3 σ active xx, outEqualX3 σ active xx))
    (fun yy => (reduceY3 σ active yy, outEqualY3 σ active yy)) id using 1
  funext xx yy zz
  simp only [OM.NNN11.edgeFactor, id_eq]

theorem residual3_edge_value [Nonempty XA] [Nonempty ZA] [Nonempty YB] [Nonempty ZB]
    [Nonempty XC] [Nonempty YC] [Nonempty ZC] (stable : ∀ s, active (σ s) ↔ active s)
    (φ : PolMul.Spectral ℂ)
    (TA : Tensor ℂ XA (X y) ZA) (TB : Tensor ℂ (X x) YB ZB) (TC : Tensor ℂ XC YC ZC)
    (K : JointComplement3 (C := C) (YC := YC) (ZB := ZB) (ZA := ZA) (XC := XC) active) :
    value φ (jointContract3 σ active TA TB TC K) ≤ value φ (residual3 σ active TA TB TC K) *
      (Fintype.card (EqualSlots σ active → ZMod 2) : ℝ) ^ Foundations.PairUnitExponents.theta φ 2 := by
  have h := value_mono φ (restricts_degenerates _ _
    (residual3_edge_restriction σ active stable TA TB TC K))
  rw [OM.NNN11.value_edgeFactor] at h
  exact h

/-- the complement of a permutation on AB: identity on the unacted digits, `Q`, `R` elsewhere -/
def productComplement3 (Q : Operator (BondBC B C YC ZB)) (R : Operator (BondCA C A ZA XC)) :
    JointComplement3 (C := C) (YC := YC) (ZB := ZB) (ZA := ZA) (XC := XC) active :=
  fun u v b b' c c' => (if u = v then 1 else 0) * Q b b' * R c c'

theorem contract3_eq_joint (fixed : ∀ s, ¬ active s → σ s = s)
    (TA : Tensor ℂ XA (X y) ZA) (TB : Tensor ℂ (X x) YB ZB) (TC : Tensor ℂ XC YC ZC)
    (Q : Operator (BondBC B C YC ZB)) (R : Operator (BondCA C A ZA XC)) :
    contract3 TA TB TC (permutationBond σ) Q R =
      jointContract3 σ active TA TB TC (productComplement3 active Q R) := by
  funext xx yy zz
  unfold contract3 jointContract3
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  unfold permutationBond
  rw [whole_delta_eq_joint σ active fixed]
  simp only [joint, productComplement3, bitBasis_apply]
  split_ifs <;> ring

theorem permutation3_edge_value [Nonempty XA] [Nonempty ZA] [Nonempty YB] [Nonempty ZB]
    [Nonempty XC] [Nonempty YC] [Nonempty ZC]
    (stable : ∀ s, active (σ s) ↔ active s) (fixed : ∀ s, ¬ active s → σ s = s)
    (φ : PolMul.Spectral ℂ)
    (TA : Tensor ℂ XA (X y) ZA) (TB : Tensor ℂ (X x) YB ZB) (TC : Tensor ℂ XC YC ZC)
    (Q : Operator (BondBC B C YC ZB)) (R : Operator (BondCA C A ZA XC)) :
    value φ (contract3 TA TB TC (permutationBond σ) Q R) ≤
      value φ (residual3 σ active TA TB TC (productComplement3 active Q R)) *
        (Fintype.card (EqualSlots σ active → ZMod 2) : ℝ) ^ Foundations.PairUnitExponents.theta φ 2 := by
  rw [contract3_eq_joint σ active fixed]
  exact residual3_edge_value σ active stable φ TA TB TC _

/-! ## Residual dimensions -/

theorem residualX3_card {xa xc : ℕ} :
    Fintype.card (ResidualX3 (XA := X xa) (XC := X xc) (C := C) σ active) =
      2 ^ (Fintype.card A * xa + Fintype.card B * x + Fintype.card C * xc -
        Fintype.card (EqualSlots σ active)) := by
  have h := equalSlots_le_row σ active
  simp only [Fintype.card_prod, Fintype.card_fin] at h
  simp only [ResidualX3, RowRemaining, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_subtype_compl, selected_row_card, X, ZMod.card, Fintype.card_fin, ← pow_mul,
    ← pow_add]
  congr 1
  rw [Nat.mul_comm (Fintype.card A) xa, Nat.mul_comm (Fintype.card C) xc]
  omega

theorem residualY3_card {yb yc : ℕ} :
    Fintype.card (ResidualY3 (YB := X yb) (YC := X yc) (C := C) σ active) =
      2 ^ (Fintype.card A * y + Fintype.card B * yb + Fintype.card C * yc -
        Fintype.card (EqualSlots σ active)) := by
  have h := equalSlots_le_col σ active
  simp only [Fintype.card_prod, Fintype.card_fin] at h
  simp only [ResidualY3, ColRemaining, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_subtype_compl, selected_col_card, X, ZMod.card, Fintype.card_fin, ← pow_mul,
    ← pow_add]
  congr 1
  rw [Nat.mul_comm (Fintype.card B) yb, Nat.mul_comm (Fintype.card C) yc]
  omega

end OM.NNN20.Mix.AB

namespace OM.NNN20.Mix.AB
open CoordinateTensor OM.NNN.Raw OM.NNN2 OM.NNN11.Network OM.NNN11.SlotExtraction
open OM.NNN11.ExtractionAB (X)
open OM.NNN11 (card_eq_change_fintypes value_le_change_fintypes outputs_binary_card)
open OM.NNN12.Codes Foundations.PairUnitExponents
set_option maxHeartbeats 2000000

variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C]
  {q k x y N : ℕ} [Fact q.Prime]

/-- a bound at one dyadic format prices every tensor whose index sets have that format -/
theorem bound_of_card_at (φ : PolMul.Spectral ℂ) {I J K : Type} [Fintype I] [Fintype J]
    [Fintype K] (v : OM.NNN12.Shape) {G : ℝ}
    (hb : ∀ U : OM.NNN12.DyadicTensor v, value φ U ≤ (2 : ℝ) ^ G)
    (hi : Fintype.card I = 2 ^ v 0) (hj : Fintype.card J = 2 ^ v 1)
    (hk : Fintype.card K = 2 ^ v 2) (T : Tensor ℂ I J K) : value φ T ≤ (2 : ℝ) ^ G := by
  let ei : X (v 0) ≃ I := Fintype.equivOfCardEq (by simp [X, hi])
  let ej : X (v 1) ≃ J := Fintype.equivOfCardEq (by simp [X, hj])
  let ek : X (v 2) ≃ K := Fintype.equivOfCardEq (by simp [X, hk])
  have hh := hb (fun a b c => T (ei a) (ej b) (ek c))
  rwa [value_reindex] at hh

/-- **A full AB correction word of a mixed network**: the
residual, of format `(|A| xa + |B| x + |C| xc - k w, |A| y + |B| yb + |C| yc - k w,
|A| za + |B| zb + |C| zc)`, is priced by any bound `G` at that format; the `k w` forced output
equalities cost `t` each. -/
theorem full_AB3 (L : OM.NNN12.BondLayout q k A B x y N) (cw : Word q N)
    (φ : PolMul.Spectral ℂ) {xa za yb zb xc yc zc : ℕ}
    (TA : Tensor ℂ (X xa) (X y) (X za)) (TB : Tensor ℂ (X x) (X yb) (X zb))
    (TC : Tensor ℂ (X xc) (X yc) (X zc))
    (Q : Operator (BondBC B C (X yc) (X zb))) (R : Operator (BondCA C A (X za) (X xc)))
    {G : ℝ}
    (hb : ∀ U : OM.NNN12.DyadicTensor
      ![Fintype.card A * xa + Fintype.card B * x + Fintype.card C * xc - k * weight cw,
        Fintype.card A * y + Fintype.card B * yb + Fintype.card C * yc - k * weight cw,
        Fintype.card A * za + Fintype.card B * zb + Fintype.card C * zc],
      value φ U ≤ (2 : ℝ) ^ G)
    (t : ℝ) (ht : theta φ 2 ≤ t) :
    value φ (contract3 TA TB TC (L.kernel cw) Q R) ≤ (2 : ℝ) ^ (G + t * (k * weight cw)) := by
  let σ := OM.NNN12.Cyclic.permutation L.coordinates cw
  let active := OM.NNN12.Cyclic.active L.coordinates cw
  let W := residual3 σ active TA TB TC (productComplement3 active Q R)
  have heq : Fintype.card (EqualSlots σ active) = k * weight cw := L.crossings cw
  have hw := bound_of_card_at φ _ hb
    (by
      have hd := residualX3_card (C := C) (xa := xa) (xc := xc) σ active
      rw [heq] at hd
      exact card_eq_change_fintypes hd)
    (by
      have hd := residualY3_card (C := C) (yb := yb) (yc := yc) σ active
      rw [heq] at hd
      exact card_eq_change_fintypes hd)
    (by
      show Fintype.card ((A → X za) × (B → X zb) × (C → X zc)) =
        2 ^ (Fintype.card A * za + Fintype.card B * zb + Fintype.card C * zc)
      simp only [Fintype.card_prod, Fintype.card_fun, X, ZMod.card, Fintype.card_fin, ← pow_mul,
        ← pow_add]
      congr 1
      ring)
    W
  have he := permutation3_edge_value σ active
    (OM.NNN12.Cyclic.stable L.coordinates cw) (OM.NNN12.Cyclic.fixed L.coordinates cw) φ
    TA TB TC Q R
  simp only [Fintype.card_fun, ZMod.card, heq, Nat.cast_pow, Nat.cast_ofNat] at he
  have hh := OM.NNN12.edge_price (k * weight cw) ht he (value_le_change_fintypes φ _ hw)
  simpa only [Nat.cast_mul] using! value_le_change_fintypes φ _ hh

end OM.NNN20.Mix.AB
