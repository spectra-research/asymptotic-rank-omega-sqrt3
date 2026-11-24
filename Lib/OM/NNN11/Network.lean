import Lib.OM.NNN10.Payload

/-! The coefficient-assignment network on three disjoint sets of labelled copies.
Each physical bond has its own pair of endpoint words. The three input dimensions
and the three ownership counts are independent. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN11.Network
open CoordinateTensor OM.NNN.Raw OM.NNN2
set_option maxHeartbeats 2000000

variable {A B C X Y Z : Type}
  [Fintype A] [Fintype B] [Fintype C]
  [Fintype X] [Fintype Y] [Fintype Z]

/-- Output blocks keep the same copy order at all three parties. -/
abbrev Outputs (A B C X : Type) := (A → X) × (B → X) × (C → X)

/-- Slots on the A--B bond: A-owned Y coordinates and B-owned X coordinates. -/
abbrev BondAB (A B X Y : Type) := (A → Y) × (B → X)
abbrev BondBC (B C Y Z : Type) := (B → Z) × (C → Y)
abbrev BondCA (C A Z X : Type) := (C → X) × (A → Z)

abbrev Operator (E : Type) := E → E → ℂ

def identity (E : Type) : Operator E := fun u v => if u = v then 1 else 0

/-- An ordered product, with no assumption that the tensor factors by digits. -/
def ordered {D : Type} [Fintype D] (T : Tensor ℂ X Y Z) :
    Tensor ℂ (D → X) (D → Y) (D → Z) :=
  fun x y z => ∏ d, T (x d) (y d) (z d)

def assemble {E : Type} (x : Outputs A B C E) : A ⊕ B ⊕ C → E :=
  Sum.elim x.1 (Sum.elim x.2.1 x.2.2)

/-- Sum only coefficient-side coordinates; passive coordinates are outputs. -/
def contract (T : Tensor ℂ X Y Z)
    (P : Operator (BondAB A B X Y)) (Q : Operator (BondBC B C Y Z))
    (R : Operator (BondCA C A Z X)) :
    Tensor ℂ (Outputs A B C X) (Outputs A B C Y) (Outputs A B C Z) :=
  fun x y z =>
    ∑ a : (A → Y) × (A → Z),
    ∑ b : (B → X) × (B → Z),
    ∑ c : (C → X) × (C → Y),
      P (a.1, x.2.1) (y.1, b.1) *
      Q (b.2, y.2.2) (z.2.1, c.2) *
      R (c.1, z.1) (x.2.2, a.2) *
      ordered T x.1 a.1 a.2 * ordered T b.1 y.2.1 b.2 * ordered T c.1 c.2 z.2.2

theorem contract_identity (T : Tensor ℂ X Y Z) :
    contract (A := A) (B := B) (C := C) T (identity _) (identity _) (identity _) =
      fun x y z => ordered T x.1 y.1 z.1 *
        ordered T x.2.1 y.2.1 z.2.1 * ordered T x.2.2 y.2.2 z.2.2 := by
  funext x y z
  simp [contract, identity, Prod.ext_iff, Fintype.sum_prod_type,
    ite_mul, mul_ite, ite_and, Finset.sum_ite_irrel, eq_comm]

/-- Identity bonds give precisely the ordered product of all labelled copies. -/
theorem contract_identity_ordered (T : Tensor ℂ X Y Z) :
    contract (A := A) (B := B) (C := C) T (identity _) (identity _) (identity _) =
      fun x y z => ordered T (assemble x) (assemble y) (assemble z) := by
  rw [contract_identity]
  funext x y z
  simp [ordered, assemble, Fintype.prod_sum_type, mul_assoc]

def factor {E I : Type} [Fintype I] (U V : I → E → ℂ) : Operator E :=
  fun a b => ∑ i, U i a * V i b

variable {P Q R : Type} [Fintype P] [Fintype Q] [Fintype R]

def leftMap (T : Tensor ℂ X Y Z)
    (U : P → BondAB A B X Y → ℂ) (V : R → BondCA C A Z X → ℂ) :
    Outputs A B C X → R × P → ℂ := fun x rp =>
  ∑ a : (A → Y) × (A → Z), U rp.2 (a.1, x.2.1) * V rp.1 (x.2.2, a.2) *
    ordered T x.1 a.1 a.2

def midMap (T : Tensor ℂ X Y Z)
    (V : P → BondAB A B X Y → ℂ) (U : Q → BondBC B C Y Z → ℂ) :
    Outputs A B C Y → Q × P → ℂ := fun y qp =>
  ∑ b : (B → X) × (B → Z), V qp.2 (y.1, b.1) * U qp.1 (b.2, y.2.2) *
    ordered T b.1 y.2.1 b.2

def rightMap (T : Tensor ℂ X Y Z)
    (U : R → BondCA C A Z X → ℂ) (V : Q → BondBC B C Y Z → ℂ) :
    Outputs A B C Z → R × Q → ℂ := fun z rq =>
  ∑ c : (C → X) × (C → Y), U rq.1 (c.1, z.1) * V rq.2 (z.2.1, c.2) *
    ordered T c.1 c.2 z.2.2

/-- Actual endpoint maps through three separately factored physical bonds.
The factor types may be empty, so this also covers a rank-zero head. -/
theorem factorized_contract (T : Tensor ℂ X Y Z)
    (Uab Vab : P → BondAB A B X Y → ℂ)
    (Ubc Vbc : Q → BondBC B C Y Z → ℂ)
    (Uca Vca : R → BondCA C A Z X → ℂ) :
    mapTensor (leftMap T Uab Vca) (midMap T Vab Ubc) (rightMap T Uca Vbc)
      (mm R Q P) = contract T (factor Uab Vab) (factor Ubc Vbc) (factor Uca Vca) := by
  funext x y z
  rw [NNN10.map_mm_rect]
  simp only [leftMap, midMap, rightMap, contract, factor, Finset.sum_mul, Finset.mul_sum]
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
      ∑ t : ((A → Y) × (A → Z)) × ((B → X) × (B → Z)) × ((C → X) × (C → Y)),
        (Uab s.2.2 (t.1.1, x.2.1) * Vca s.1 (x.2.2, t.1.2) *
          ordered T x.1 t.1.1 t.1.2) *
        (Vab s.2.2 (y.1, t.2.1.1) * Ubc s.2.1 (t.2.1.2, y.2.2) *
          ordered T t.2.1.1 y.2.1 t.2.1.2) *
        (Uca s.1 (t.2.2.1, z.1) * Vbc s.2.1 (z.2.1, t.2.2.2) *
          ordered T t.2.2.1 t.2.2.2 z.2.2) := by simp only [Fintype.sum_prod_type]
    _ = ∑ t : ((A → Y) × (A → Z)) × ((B → X) × (B → Z)) × ((C → X) × (C → Y)),
      ∑ s : R × Q × P,
        (Uab s.2.2 (t.1.1, x.2.1) * Vca s.1 (x.2.2, t.1.2) *
          ordered T x.1 t.1.1 t.1.2) *
        (Vab s.2.2 (y.1, t.2.1.1) * Ubc s.2.1 (t.2.1.2, y.2.2) *
          ordered T t.2.1.1 y.2.1 t.2.1.2) *
        (Uca s.1 (t.2.2.1, z.1) * Vbc s.2.1 (z.2.1, t.2.2.2) *
          ordered T t.2.2.1 t.2.2.2 z.2.2) := Finset.sum_comm
    _ = _ := by
      simp only [Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
      repeat' (apply Finset.sum_congr rfl; intro _ _)
      rw [NNN3.sum_reverse]
      repeat' (apply Finset.sum_congr rfl; intro _ _)
      ac_rfl

theorem compressed_restriction (T : Tensor ℂ X Y Z)
    (Uab Vab : P → BondAB A B X Y → ℂ)
    (Ubc Vbc : Q → BondBC B C Y Z → ℂ)
    (Uca Vca : R → BondCA C A Z X → ℂ) :
    Restricts (mm R Q P) (contract T (factor Uab Vab) (factor Ubc Vbc) (factor Uca Vca)) :=
  ⟨leftMap T Uab Vca, midMap T Vab Ubc, rightMap T Uca Vbc,
    factorized_contract T Uab Vab Ubc Vbc Uca Vca⟩

lemma bondAB_card : Fintype.card (BondAB A B X Y) =
    Fintype.card Y ^ Fintype.card A * Fintype.card X ^ Fintype.card B := by
  simp [BondAB]

lemma bondBC_card : Fintype.card (BondBC B C Y Z) =
    Fintype.card Z ^ Fintype.card B * Fintype.card Y ^ Fintype.card C := by
  simp [BondBC]

lemma bondCA_card : Fintype.card (BondCA C A Z X) =
    Fintype.card X ^ Fintype.card C * Fintype.card Z ^ Fintype.card A := by
  simp [BondCA]

/-- A fixed enumeration of the 21/21/28 ownership blocks. -/
def copies70 : (Fin 21 ⊕ Fin 21 ⊕ Fin 28) ≃ Fin 70 :=
  (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv

def outputs70 {E : Type} (x : Outputs (Fin 21) (Fin 21) (Fin 28) E) : Fin 70 → E :=
  assemble x ∘ copies70.symm

theorem contract70_identity (T : Tensor ℂ X Y Z) :
    contract (A := Fin 21) (B := Fin 21) (C := Fin 28)
      T (identity _) (identity _) (identity _) =
      fun x y z => ordered T (outputs70 x) (outputs70 y) (outputs70 z) := by
  rw [contract_identity_ordered]
  funext x y z
  exact (copies70.symm.prod_comp (fun d => T (assemble x d) (assemble y d) (assemble z d))).symm

end OM.NNN11.Network
