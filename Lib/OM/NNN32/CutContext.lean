import Lib.OM.NNN32.PriceDiscount
import Lib.OM.NNN32.Cuts

/-! # Removing the two marked bonds of a network

A context retains the unmarked graph and a local half-factor at each of four
corners. The two diagonals have register types A and B. Splitting a register
index into a common channel and a residual channel leaves equality on the
residual indices while the common channels accept a four-leg tensor.
-/

noncomputable section
open scoped Classical

namespace OM.NNN32

open Semicontinuity OM.NNN30.Net

abbrev registers (A B : Type) : Fin 4 → Type := ![A,B,B,A]
abbrev assignments {V : Type} {f : Fin 4 → ℕ+} (N : FourNetwork V f) :=
  (s : N.graph.V) → N.graph.T s

structure CutContext (V : Type) (f : Fin 4 → ℕ+) (A B : Type) where
  net : FourNetwork V f
  sites : Fin 4 → V
  half : (i : Fin 4) → registers A B i → assignments net → ℂ

namespace CutContext

variable {V A B : Type} {f : Fin 4 → ℕ+} (C : CutContext V f A B)
variable [Fintype A] [Fintype B]

instance regFinite : (i : Fin 4) → Fintype (registers A B i)
  | 0 => (inferInstance : Fintype A)
  | 1 => (inferInstance : Fintype B)
  | 2 => (inferInstance : Fintype B)
  | 3 => (inferInstance : Fintype A)

abbrev labels (_C : CutContext V f A B) := (i : Fin 4) → registers A B i

def Local (τ : Fin 4 → V) := C.net.Local τ ∧ ∀ i z, C.net.graph.DepAt (C.sites i) (C.half i z)

def exterior (x : assignments C.net) (a : (i : Fin 4) → Fin (f i)) : ℂ :=
  (∏ i, C.net.out i x (a i)) * ∏ k, C.net.graph.F k x

/-- Contract the removed registers as equality wires. -/
def closed : KTensor ℂ f := fun a => ∑ x, C.exterior x a *
  ((∑ z : A, C.half 0 z x * C.half 3 z x) * (∑ w : B, C.half 1 w x * C.half 2 w x))

variable {D : ℕ+} {r s : ℕ}
variable (p : A ↪ Fin (D:ℕ) × Fin r) (q : B ↪ Fin (D:ℕ) × Fin s)

def channel : (i : Fin 4) → registers A B i → Fin (D:ℕ)
  | 0, z => (p z).1
  | 1, z => (q z).1
  | 2, z => (q z).1
  | 3, z => (p z).1

def common (c : (i : Fin 4) → registers A B i) : Fin 4 → Fin (D:ℕ) :=
  fun i => channel p q i (c i)

def residual (c : (i : Fin 4) → registers A B i) : ℂ :=
  (if (p (c 0)).2=(p (c 3)).2 then 1 else 0) * (if (q (c 1)).2=(q (c 2)).2 then 1 else 0)

def insert (T : Four D) : KTensor ℂ f := fun a => ∑ x, C.exterior x a *
  ∑ c : C.labels, ((∏ i, C.half i (c i) x) * residual p q c) * T (common p q c)

lemma insert_add (S T : Four D) : C.insert p q (S+T) = C.insert p q S + C.insert p q T := by
  funext a
  simp [insert,mul_add,Finset.sum_add_distrib]

private def tuple : ((i : Fin 4) → registers A B i) ≃ A × B × B × A where
  toFun x := (x 0,x 1,x 2,x 3)
  invFun a
    | 0 => a.1
    | 1 => a.2.1
    | 2 => a.2.2.1
    | 3 => a.2.2.2
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv a := rfl

lemma insert_crossing : C.insert p q (crossing D) = C.closed := by
  funext a
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  have coeff (c : C.labels) : residual p q c * crossing D (common p q c) =
      if c 0=c 3 ∧ c 1=c 2 then 1 else 0 := by
    have h1 : (p (c 0)).1=(p (c 3)).1 ∧ (p (c 0)).2=(p (c 3)).2 ↔ c 0=c 3 :=
      Prod.ext_iff.symm.trans p.injective.eq_iff
    have h2 : (q (c 1)).1=(q (c 2)).1 ∧ (q (c 1)).2=(q (c 2)).2 ↔ c 1=c 2 :=
      Prod.ext_iff.symm.trans q.injective.eq_iff
    simp [residual,crossing,matching,common,channel]
    split_ifs <;> simp_all
  simp_rw [mul_assoc,coeff]
  rw [← (tuple (A := A) (B := B)).symm.sum_comp]
  simp only [Fintype.sum_prod_type,Fin.prod_univ_four]
  change (∑ a : A, ∑ b : B, ∑ y : B, ∑ z : A,
    C.half 0 a x * C.half 1 b x * C.half 2 y x * C.half 3 z x *
      (if a=z ∧ b=y then 1 else 0)) = _
  simp [ite_and,mul_ite,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

end CutContext

end OM.NNN32
