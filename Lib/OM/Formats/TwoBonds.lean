import Lib.OM.NNN32.MarkedBonds

/-! # Factoring unequal channels out of two marked bonds -/

noncomputable section
open scoped Classical
namespace OM.Formats

open NNN32 Semicontinuity
abbrev ends (D E : ℕ+) : Fin 4 → ℕ+ := ![D,E,E,D]
abbrev Channels (D E : ℕ+) := (i : Fin 4) → Fin (ends D E i)
abbrev Piece (D E : ℕ+) := Fin (D:ℕ) → Fin (E:ℕ) → Fin (E:ℕ) → Fin (D:ℕ) → ℂ

namespace TwoBonds

variable {V A B : Type} [Fintype A] [Fintype B] {f : Fin 4 → ℕ+}
    {D E : ℕ+} {r s : ℕ}
variable (C : CutContext V f A B) (p : A ↪ Index D × Fin r) (q : B ↪ Index E × Fin s)

def channel : (i : Fin 4) → registers A B i → Fin (ends D E i)
  | 0, z => (p z).1
  | 1, z => (q z).1
  | 2, z => (q z).1
  | 3, z => (p z).1

def wires (c : C.labels) : Channels D E := fun i => channel p q i (c i)

def rest (c : C.labels) : ℂ :=
  (if (p (c 0)).2 = (p (c 3)).2 then 1 else 0) * (if (q (c 1)).2 = (q (c 2)).2 then 1 else 0)

def insert (P : Piece D E) : KTensor ℂ f := fun a => ∑ x, C.exterior x a *
  ∑ c : C.labels, ((∏ i, C.half i (c i) x) * rest C p q c) *
    P (p (c 0)).1 (q (c 1)).1 (q (c 2)).1 (p (c 3)).1

private def tuple : ((i : Fin 4) → registers A B i) ≃ A × B × B × A where
  toFun x := (x 0,x 1,x 2,x 3)
  invFun a := fun | 0 => a.1 | 1 => a.2.1 | 2 => a.2.2.1 | 3 => a.2.2.2
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv _ := rfl

theorem sum_insert {K : ℕ} (P : Fin K → Piece D E)
    (sum : ∀ i j k l, ∑ u, P u i j k l = if i=l ∧ j=k then 1 else 0) :
    C.closed = ∑ u, insert C p q (P u) := by
  funext a
  simp only [Finset.sum_apply, insert]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp only [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, sum, mul_assoc]
  have coeff (c : C.labels) : rest C p q c *
      (if (p (c 0)).1=(p (c 3)).1 ∧ (q (c 1)).1=(q (c 2)).1 then 1 else 0) =
      if c 0=c 3 ∧ c 1=c 2 then 1 else 0 := by
    have h1 : (p (c 0)).1=(p (c 3)).1 ∧ (p (c 0)).2=(p (c 3)).2 ↔ c 0=c 3 :=
      Prod.ext_iff.symm.trans p.injective.eq_iff
    have h2 : (q (c 1)).1=(q (c 2)).1 ∧ (q (c 1)).2=(q (c 2)).2 ↔ c 1=c 2 :=
      Prod.ext_iff.symm.trans q.injective.eq_iff
    unfold rest; split_ifs <;> simp_all
  simp_rw [coeff]
  rw [← (tuple (A := A) (B := B)).symm.sum_comp]
  simp only [Fintype.sum_prod_type, Fin.prod_univ_four]
  symm
  change (∑ a : A, ∑ b : B, ∑ y : B, ∑ z : A,
    C.half 0 a x * C.half 1 b x * C.half 2 y x * C.half 3 z x *
      (if a=z ∧ b=y then 1 else 0)) = _
  simp [ite_and,mul_ite,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro a _
  ring

end TwoBonds
end OM.Formats
