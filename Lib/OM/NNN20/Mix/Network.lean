import Lib.OM.NNN11.NetworkPowers
import Lib.OM.NNN11.Telescope
import Lib.OM.NNN11.Retention

/-! # Mixed coefficient networks

NNN.11's `Network.contract` places copies of one tensor at the three parties. The catalysed
source uses copies of the priced tensor `U` at one party and copies of the catalyst at the other
two; its identities never use that the copies are equal. `contract3 TA TB TC`
has the copies `A` of `TA` (owned by party 0), `B` of `TB` (party 1), `C` of `TC` (party 2), with
their own index types; `contract3 T T T = contract T` (`contract3_self`).

* `contract3_identity`, `value_contract3_identity`: identity wiring is the product of the three
  ordered products, of value `φ(TA)^|A| φ(TB)^|B| φ(TC)^|C|`.
* `linear3AB/BC/CA`: the network is linear in each bond operator (the telescope).
* `compressed_restriction3`: factorised bond operators give a restriction of `mm R Q P` (the head).
* `retained3BC`, `value_retained3BC`: identities on bonds AB and CA retain the class `A`:
  the network is the pair network of `TB`, `TC` times `TA^{⊗A}`. -/

noncomputable section
open scoped BigOperators Classical
namespace OM.NNN20.Mix
open CoordinateTensor OM.NNN.Raw OM.NNN2 OM.NNN3 OM.NNN11.Network

variable {A B C XA YA ZA XB YB ZB XC YC ZC : Type}
  [Fintype A] [Fintype B] [Fintype C]
  [Fintype XA] [Fintype YA] [Fintype ZA] [Fintype XB] [Fintype YB] [Fintype ZB]
  [Fintype XC] [Fintype YC] [Fintype ZC]

/-- the mixed coefficient network -/
def contract3 (TA : Tensor ℂ XA YA ZA) (TB : Tensor ℂ XB YB ZB) (TC : Tensor ℂ XC YC ZC)
    (P : Operator (BondAB A B XB YA)) (Q : Operator (BondBC B C YC ZB))
    (R : Operator (BondCA C A ZA XC)) :
    Tensor ℂ ((A → XA) × (B → XB) × (C → XC)) ((A → YA) × (B → YB) × (C → YC))
      ((A → ZA) × (B → ZB) × (C → ZC)) :=
  fun x y z =>
    ∑ a : (A → YA) × (A → ZA),
    ∑ b : (B → XB) × (B → ZB),
    ∑ c : (C → XC) × (C → YC),
      P (a.1, x.2.1) (y.1, b.1) *
      Q (b.2, y.2.2) (z.2.1, c.2) *
      R (c.1, z.1) (x.2.2, a.2) *
      ordered TA x.1 a.1 a.2 * ordered TB b.1 y.2.1 b.2 * ordered TC c.1 c.2 z.2.2

lemma contract3_self {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] (T : Tensor ℂ X Y Z)
    (P : Operator (BondAB A B X Y)) (Q : Operator (BondBC B C Y Z))
    (R : Operator (BondCA C A Z X)) :
    contract3 (A := A) (B := B) (C := C) T T T P Q R = contract T P Q R := rfl

/-- **Identity wiring**. -/
theorem contract3_identity (TA : Tensor ℂ XA YA ZA) (TB : Tensor ℂ XB YB ZB)
    (TC : Tensor ℂ XC YC ZC) :
    contract3 (A := A) (B := B) (C := C) TA TB TC (identity _) (identity _) (identity _) =
      fun x y z => ordered TA x.1 y.1 z.1 *
        ordered TB x.2.1 y.2.1 z.2.1 * ordered TC x.2.2 y.2.2 z.2.2 := by
  funext x y z
  simp [contract3, identity, Prod.ext_iff, Fintype.sum_prod_type,
    ite_mul, mul_ite, ite_and, Finset.sum_ite_irrel, eq_comm]

theorem value_contract3_identity [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [Nonempty XA] [Nonempty YA] [Nonempty ZA] [Nonempty XB] [Nonempty YB] [Nonempty ZB]
    [Nonempty XC] [Nonempty YC] [Nonempty ZC]
    (φ : PolMul.Spectral ℂ) (TA : Tensor ℂ XA YA ZA) (TB : Tensor ℂ XB YB ZB)
    (TC : Tensor ℂ XC YC ZC) :
    value φ (contract3 (A := A) (B := B) (C := C) TA TB TC (identity _) (identity _)
      (identity _)) =
      value φ TA ^ Fintype.card A * value φ TB ^ Fintype.card B * value φ TC ^ Fintype.card C := by
  rw [contract3_identity]
  have e : (fun (x : (A → XA) × (B → XB) × (C → XC)) (y : (A → YA) × (B → YB) × (C → YC))
      (z : (A → ZA) × (B → ZB) × (C → ZC)) => ordered TA x.1 y.1 z.1 *
        ordered TB x.2.1 y.2.1 z.2.1 * ordered TC x.2.2 y.2.2 z.2.2) =
      tensorProduct (ordered (D := A) TA) (tensorProduct (ordered (D := B) TB)
        (ordered (D := C) TC)) := by
    funext x y z
    simp only [tensorProduct]
    ring
  rw [e, value_product', value_product', value_ordered, value_ordered, value_ordered]
  ring

/-! ## Linearity in each bond operator (the telescope) -/

def linear3AB (TA : Tensor ℂ XA YA ZA) (TB : Tensor ℂ XB YB ZB) (TC : Tensor ℂ XC YC ZC)
    (Q : Operator (BondBC B C YC ZB)) (R : Operator (BondCA C A ZA XC)) :
    Operator (BondAB A B XB YA) →ₗ[ℂ]
      Tensor ℂ ((A → XA) × (B → XB) × (C → XC)) ((A → YA) × (B → YB) × (C → YC))
        ((A → ZA) × (B → ZB) × (C → ZC)) where
  toFun P := contract3 TA TB TC P Q R
  map_add' P P' := by
    funext x y z
    simp [contract3, add_mul, Finset.sum_add_distrib]
  map_smul' z P := by
    funext x y w
    simp [contract3, Finset.mul_sum, mul_assoc]

def linear3BC (TA : Tensor ℂ XA YA ZA) (TB : Tensor ℂ XB YB ZB) (TC : Tensor ℂ XC YC ZC)
    (P : Operator (BondAB A B XB YA)) (R : Operator (BondCA C A ZA XC)) :
    Operator (BondBC B C YC ZB) →ₗ[ℂ]
      Tensor ℂ ((A → XA) × (B → XB) × (C → XC)) ((A → YA) × (B → YB) × (C → YC))
        ((A → ZA) × (B → ZB) × (C → ZC)) where
  toFun Q := contract3 TA TB TC P Q R
  map_add' Q Q' := by
    funext x y z
    simp [contract3, add_mul, mul_add, Finset.sum_add_distrib]
  map_smul' z Q := by
    funext x y w
    simp only [contract3, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
    repeat' (apply Finset.sum_congr rfl; intro _ _)
    ring

def linear3CA (TA : Tensor ℂ XA YA ZA) (TB : Tensor ℂ XB YB ZB) (TC : Tensor ℂ XC YC ZC)
    (P : Operator (BondAB A B XB YA)) (Q : Operator (BondBC B C YC ZB)) :
    Operator (BondCA C A ZA XC) →ₗ[ℂ]
      Tensor ℂ ((A → XA) × (B → XB) × (C → XC)) ((A → YA) × (B → YB) × (C → YC))
        ((A → ZA) × (B → ZB) × (C → ZC)) where
  toFun R := contract3 TA TB TC P Q R
  map_add' R R' := by
    funext x y z
    simp [contract3, add_mul, mul_add, Finset.sum_add_distrib]
  map_smul' z R := by
    funext x y w
    simp only [contract3, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
    repeat' (apply Finset.sum_congr rfl; intro _ _)
    ring

/-! ## The head -/

variable {P Q R : Type} [Fintype P] [Fintype Q] [Fintype R]

def leftMap3 (TA : Tensor ℂ XA YA ZA)
    (U : P → BondAB A B XB YA → ℂ) (V : R → BondCA C A ZA XC → ℂ) :
    ((A → XA) × (B → XB) × (C → XC)) → R × P → ℂ := fun x rp =>
  ∑ a : (A → YA) × (A → ZA), U rp.2 (a.1, x.2.1) * V rp.1 (x.2.2, a.2) *
    ordered TA x.1 a.1 a.2

def midMap3 (TB : Tensor ℂ XB YB ZB)
    (V : P → BondAB A B XB YA → ℂ) (U : Q → BondBC B C YC ZB → ℂ) :
    ((A → YA) × (B → YB) × (C → YC)) → Q × P → ℂ := fun y qp =>
  ∑ b : (B → XB) × (B → ZB), V qp.2 (y.1, b.1) * U qp.1 (b.2, y.2.2) *
    ordered TB b.1 y.2.1 b.2

def rightMap3 (TC : Tensor ℂ XC YC ZC)
    (U : R → BondCA C A ZA XC → ℂ) (V : Q → BondBC B C YC ZB → ℂ) :
    ((A → ZA) × (B → ZB) × (C → ZC)) → R × Q → ℂ := fun z rq =>
  ∑ c : (C → XC) × (C → YC), U rq.1 (c.1, z.1) * V rq.2 (z.2.1, c.2) *
    ordered TC c.1 c.2 z.2.2

theorem factorized_contract3 (TA : Tensor ℂ XA YA ZA) (TB : Tensor ℂ XB YB ZB)
    (TC : Tensor ℂ XC YC ZC)
    (Uab Vab : P → BondAB A B XB YA → ℂ)
    (Ubc Vbc : Q → BondBC B C YC ZB → ℂ)
    (Uca Vca : R → BondCA C A ZA XC → ℂ) :
    mapTensor (leftMap3 TA Uab Vca) (midMap3 TB Vab Ubc) (rightMap3 TC Uca Vbc)
      (mm R Q P) = contract3 TA TB TC (factor Uab Vab) (factor Ubc Vbc) (factor Uca Vca) := by
  funext x y z
  rw [NNN10.map_mm_rect]
  simp only [leftMap3, midMap3, rightMap3, contract3, factor, Finset.sum_mul, Finset.mul_sum]
  conv_lhs =>
    arg 2; ext r
    arg 2; ext q
    arg 2; ext p
    rw [NNN3.sum_reverse]
  conv_rhs =>
    arg 2; ext a
    arg 2; ext b
    arg 2; ext c
    rw [NNN3.sum_reverse]
  calc
    _ = ∑ s : R × Q × P,
      ∑ t : ((A → YA) × (A → ZA)) × ((B → XB) × (B → ZB)) × ((C → XC) × (C → YC)),
        (Uab s.2.2 (t.1.1, x.2.1) * Vca s.1 (x.2.2, t.1.2) *
          ordered TA x.1 t.1.1 t.1.2) *
        (Vab s.2.2 (y.1, t.2.1.1) * Ubc s.2.1 (t.2.1.2, y.2.2) *
          ordered TB t.2.1.1 y.2.1 t.2.1.2) *
        (Uca s.1 (t.2.2.1, z.1) * Vbc s.2.1 (z.2.1, t.2.2.2) *
          ordered TC t.2.2.1 t.2.2.2 z.2.2) := by simp only [Fintype.sum_prod_type]
    _ = ∑ t : ((A → YA) × (A → ZA)) × ((B → XB) × (B → ZB)) × ((C → XC) × (C → YC)),
      ∑ s : R × Q × P,
        (Uab s.2.2 (t.1.1, x.2.1) * Vca s.1 (x.2.2, t.1.2) *
          ordered TA x.1 t.1.1 t.1.2) *
        (Vab s.2.2 (y.1, t.2.1.1) * Ubc s.2.1 (t.2.1.2, y.2.2) *
          ordered TB t.2.1.1 y.2.1 t.2.1.2) *
        (Uca s.1 (t.2.2.1, z.1) * Vbc s.2.1 (z.2.1, t.2.2.2) *
          ordered TC t.2.2.1 t.2.2.2 z.2.2) := Finset.sum_comm
    _ = _ := by
      simp only [Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
      repeat' (apply Finset.sum_congr rfl; intro _ _)
      rw [NNN3.sum_reverse]
      repeat' (apply Finset.sum_congr rfl; intro _ _)
      ac_rfl

theorem compressed_restriction3 (TA : Tensor ℂ XA YA ZA) (TB : Tensor ℂ XB YB ZB)
    (TC : Tensor ℂ XC YC ZC)
    (Uab Vab : P → BondAB A B XB YA → ℂ)
    (Ubc Vbc : Q → BondBC B C YC ZB → ℂ)
    (Uca Vca : R → BondCA C A ZA XC → ℂ) :
    Restricts (mm R Q P)
      (contract3 TA TB TC (factor Uab Vab) (factor Ubc Vbc) (factor Uca Vca)) :=
  ⟨leftMap3 TA Uab Vca, midMap3 TB Vab Ubc, rightMap3 TC Uca Vbc,
    factorized_contract3 TA TB TC Uab Vab Ubc Vbc Uca Vca⟩

/-! ## Retention of the class `A` -/

/-- the pair network of the classes `B`, `C` with the operator `Q` on bond BC -/
def pair3BC (TB : Tensor ℂ XB YB ZB) (TC : Tensor ℂ XC YC ZC) (Q : Operator (BondBC B C YC ZB)) :
    Tensor ℂ ((B → XB) × (C → XC)) ((B → YB) × (C → YC)) ((B → ZB) × (C → ZC)) :=
  fun x y z => ∑ b, ∑ c,
    Q (b, y.2) (z.1, c) * ordered TB x.1 y.1 b * ordered TC x.2 c z.2

theorem retained3BC (TA : Tensor ℂ XA YA ZA) (TB : Tensor ℂ XB YB ZB) (TC : Tensor ℂ XC YC ZC)
    (Q : Operator (BondBC B C YC ZB)) :
    contract3 (A := A) TA TB TC (identity _) Q (identity _) =
      fun x y z => pair3BC TB TC Q x.2 y.2 z.2 * ordered TA x.1 y.1 z.1 := by
  funext x y z
  simp [contract3, identity, pair3BC, Prod.ext_iff, Fintype.sum_prod_type,
    ite_mul, mul_ite, ite_and, Finset.sum_ite_irrel, Finset.sum_mul, Finset.mul_sum,
    mul_comm, mul_left_comm, mul_assoc]

theorem value_retained3BC [DecidableEq A] [Nonempty XA] [Nonempty YA] [Nonempty ZA]
    [Nonempty XB] [Nonempty YB] [Nonempty ZB] [Nonempty XC] [Nonempty YC] [Nonempty ZC]
    (φ : PolMul.Spectral ℂ) (TA : Tensor ℂ XA YA ZA) (TB : Tensor ℂ XB YB ZB)
    (TC : Tensor ℂ XC YC ZC) (Q : Operator (BondBC B C YC ZB)) :
    value φ (contract3 (A := A) TA TB TC (identity _) Q (identity _)) =
      value φ (pair3BC TB TC Q) * value φ TA ^ Fintype.card A := by
  rw [retained3BC]
  have h := value_reindex φ (tensorProduct (pair3BC TB TC Q) (ordered (D := A) TA))
    (Equiv.prodComm _ _) (Equiv.prodComm _ _) (Equiv.prodComm _ _)
  rw [value_product', value_ordered] at h
  exact h

/-- the pair network of a single tensor is NNN.11's (`pair3BC T T = pairBC T`) -/
lemma pair3BC_self {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] (T : Tensor ℂ X Y Z)
    (Q : Operator (BondBC B C Y Z)) : pair3BC T T Q = pairBC T Q := rfl

end OM.NNN20.Mix
