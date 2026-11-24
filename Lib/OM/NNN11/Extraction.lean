import Lib.OM.NNN11.SlotExtraction
import Lib.OM.NNN11.Retention
import Lib.OM.NNN10.Extraction

/-! Literal AB extraction for the entire rectangular coefficient network.
The complement may jointly couple all remaining AB digits and both other bonds. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN11.ExtractionAB
open CoordinateTensor OM.NNN.Raw OM.NNN2 Network SlotExtraction Wiring
set_option maxHeartbeats 1000000

variable {A B C Z : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype Z]
  {x y : ℕ}

abbrev X (x : ℕ) := Fin x → ZMod 2
abbrev Slot (A B : Type) (x y : ℕ) := (A × Fin y) ⊕ (B × Fin x)

variable (σ : Slot A B x y ≃ Slot A B x y) (active : Slot A B x y → Prop)

abbrev Complement := {s : Slot A B x y // ¬ active s} → ZMod 2

abbrev JointComplement := Complement active → Complement active →
  BondBC B C (X y) Z → BondBC B C (X y) Z →
  BondCA C A Z (X x) → BondCA C A Z (X x) → ℂ

/-- The same coefficient sums as Network.contract, with a single arbitrary
joint complementary operator. Coefficients of T are never split into digits. -/
def jointContract (T : Tensor ℂ (X x) (X y) Z) (K : JointComplement (C := C) (Z := Z) active) :
    Tensor ℂ (Outputs A B C (X x)) (Outputs A B C (X y)) (Outputs A B C Z) :=
  fun xx yy zz =>
    ∑ a : (A → X y) × (A → Z),
    ∑ b : (B → X x) × (B → Z),
    ∑ c : (C → X x) × (C → X y),
      joint σ active
        (fun r s => K r s (b.2, yy.2.2) (zz.2.1, c.2) (c.1, zz.1) (xx.2.2, a.2))
        (Sum.elim (Function.uncurry a.1) (Function.uncurry xx.2.1))
        (Sum.elim (Function.uncurry yy.1) (Function.uncurry b.1)) *
      ordered T xx.1 a.1 a.2 * ordered T b.1 yy.2.1 b.2 * ordered T c.1 c.2 zz.2.2

def normalX (xx : Outputs A B C (X x)) : Outputs A B C (X x) :=
  (xx.1, (fun b d => passiveRow σ active 0 (Function.uncurry xx.2.1) (b, d)), xx.2.2)

def normalY (yy : Outputs A B C (X y)) : Outputs A B C (X y) :=
  ((fun a d => passiveCol σ active 0 (Function.uncurry yy.1) (a, d)), yy.2.1, yy.2.2)

def outEqualX (xx : Outputs A B C (X x)) : EqualSlots σ active → ZMod 2 :=
  equalRow σ active 0 (Function.uncurry xx.2.1)

def outEqualY (yy : Outputs A B C (X y)) : EqualSlots σ active → ZMod 2 :=
  equalCol σ active 0 (Function.uncurry yy.1)

/-- Every extracted equality is independent of all coefficient-side sums and
of an arbitrary joint complement. This includes a word with no crossings. -/
theorem jointContract_extract (stable : ∀ s, active (σ s) ↔ active s)
    (T : Tensor ℂ (X x) (X y) Z) (K : JointComplement (C := C) (Z := Z) active)
    (xx : Outputs A B C (X x)) (yy : Outputs A B C (X y)) (zz : Outputs A B C Z) :
    jointContract σ active T K xx yy zz =
      if outEqualX σ active xx = outEqualY σ active yy then
        jointContract σ active T K (normalX σ active xx) (normalY σ active yy) zz else 0 := by
  unfold jointContract
  by_cases h : outEqualX σ active xx = outEqualY σ active yy
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

abbrev ResidualX := (A → X x) × RowRemaining (E := ZMod 2) σ active × (C → X x)
abbrev ResidualY := ColRemaining (E := ZMod 2) σ active × (B → X y) × (C → X y)

def reduceX (xx : Outputs A B C (X x)) : ResidualX (C := C) σ active :=
  (xx.1, rowRest σ active (Function.uncurry xx.2.1), xx.2.2)

def reduceY (yy : Outputs A B C (X y)) : ResidualY (C := C) σ active :=
  (colRest σ active (Function.uncurry yy.1), yy.2.1, yy.2.2)

def insertX (xx : ResidualX (C := C) σ active) : Outputs A B C (X x) :=
  (xx.1, (fun b d => fillRow σ active 0 xx.2.1 (b, d)), xx.2.2)

def insertY (yy : ResidualY (C := C) σ active) : Outputs A B C (X y) :=
  ((fun a d => fillCol σ active 0 yy.1 (a, d)), yy.2.1, yy.2.2)

def residual (T : Tensor ℂ (X x) (X y) Z) (K : JointComplement (C := C) (Z := Z) active) :
    Tensor ℂ (ResidualX (C := C) σ active) (ResidualY (C := C) σ active) (Outputs A B C Z) :=
  fun xx yy zz => jointContract σ active T K (insertX σ active xx) (insertY σ active yy) zz

theorem residual_factorization (stable : ∀ s, active (σ s) ↔ active s)
    (T : Tensor ℂ (X x) (X y) Z) (K : JointComplement (C := C) (Z := Z) active) :
    jointContract σ active T K = fun xx yy zz =>
      if outEqualX σ active xx = outEqualY σ active yy then
        residual σ active T K (reduceX σ active xx) (reduceY σ active yy) zz else 0 := by
  funext xx yy zz
  rw [jointContract_extract σ active stable]
  simp only [normalX, normalY, passiveRow_eq_fill, passiveCol_eq_fill,
    residual, reduceX, reduceY, insertX, insertY]

end OM.NNN11.ExtractionAB

namespace OM.NNN11
open CoordinateTensor OM.NNN.Raw OM.NNN2

theorem starAB {A B C R Q E : Type} [Fintype R] [Fintype Q] [Fintype E]
    (rx : A → R) (sx : A → E) (ry : B → Q) (sy : B → E)
    (W : R → Q → C → ℂ) :
    Restricts (mm R Q E) (fun x y z => if sx x = sy y then W (rx x) (ry y) z else 0) := by
  refine ⟨(fun x => identityRows _ (rx x, sx x)),
    (fun y => identityRows _ (ry y, sy y)), (fun z r => W r.1 r.2 z), ?_⟩
  funext x y z
  simp [NNN10.map_mm_rect, identityRows, Prod.ext_iff, ite_mul, mul_ite, ite_and,
    Finset.sum_ite_irrel, eq_comm]

namespace ExtractionAB
open Network SlotExtraction Wiring

variable {A B C Z : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype Z] {x y : ℕ}
  (σ : Slot A B x y ≃ Slot A B x y) (active : Slot A B x y → Prop)

/-- Actual local star maps for the full rectangular residual. -/
theorem jointContract_restriction (stable : ∀ s, active (σ s) ↔ active s)
    (T : Tensor ℂ (X x) (X y) Z) (K : JointComplement (C := C) (Z := Z) active) :
    Restricts (mm (ResidualX (C := C) σ active) (ResidualY (C := C) σ active)
      (EqualSlots σ active → ZMod 2)) (jointContract σ active T K) := by
  rw [residual_factorization σ active stable]
  convert! starAB (reduceX σ active) (outEqualX σ active)
    (reduceY σ active) (outEqualY σ active) (residual σ active T K) using 1
  funext xx yy zz
  split_ifs <;> rfl

end ExtractionAB
end OM.NNN11
