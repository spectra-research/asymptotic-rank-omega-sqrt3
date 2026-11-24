/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Foundations.Tensors.Semicontinuity.TensorSemiring

/-! # Coordinate tuples and Kronecker product indices -/

namespace Semicontinuity

/-- Split all the indices of a Kronecker product into the two component tuples. -/
def kronIndexEquiv {k : ℕ} {d₁ d₂ : Fin k → ℕ+} :
    ((i : Fin k) → Fin (d₁ i * d₂ i : ℕ+)) ≃
      ((i : Fin k) → Fin (d₁ i)) × ((i : Fin k) → Fin (d₂ i)) :=
  (Equiv.piCongrRight (fun i => kronDecodeEquiv (d₁ := d₁ i) (d₂ := d₂ i))).trans
    (Equiv.arrowProdEquivProdArrow _ _ _)

end Semicontinuity

namespace Foundations.HyperbolicLift

variable {F : Type*}

/-- The multi-index of a `3`-mode tensor with prescribed coordinates. -/
def idx3 {d : Fin 3 → ℕ+} (a : Fin (d 0)) (b : Fin (d 1)) (c : Fin (d 2)) :
    ∀ i : Fin 3, Fin (d i) :=
  Fin.cases a (Fin.cases b (Fin.cases c (fun i => i.elim0)))

@[simp] lemma idx3_zero {d : Fin 3 → ℕ+} (a : Fin (d 0)) (b : Fin (d 1)) (c : Fin (d 2)) :
    idx3 a b c 0 = a := rfl

@[simp] lemma idx3_one {d : Fin 3 → ℕ+} (a : Fin (d 0)) (b : Fin (d 1)) (c : Fin (d 2)) :
    idx3 a b c 1 = b := rfl

@[simp] lemma idx3_two {d : Fin 3 → ℕ+} (a : Fin (d 0)) (b : Fin (d 1)) (c : Fin (d 2)) :
    idx3 a b c 2 = c := rfl

@[simp] lemma idx3_eta {d : Fin 3 → ℕ+} (ρ : ∀ i : Fin 3, Fin (d i)) :
    idx3 (ρ 0) (ρ 1) (ρ 2) = ρ := by
  funext i
  fin_cases i <;> rfl

/-- A dependent triple of leg matrices, as one family indexed by `Fin 3`. -/
def legTriple {dS d : Fin 3 → ℕ+}
    (P₀ : Fin (dS 0) → Fin (d 0) → F) (P₁ : Fin (dS 1) → Fin (d 1) → F)
    (P₂ : Fin (dS 2) → Fin (d 2) → F) :
    ∀ i : Fin 3, Fin (dS i) → Fin (d i) → F :=
  Fin.cases P₀ (Fin.cases P₁ (Fin.cases P₂ (fun i => i.elim0)))

@[simp] lemma legTriple_zero {dS d : Fin 3 → ℕ+}
    (P₀ : Fin (dS 0) → Fin (d 0) → F) (P₁ : Fin (dS 1) → Fin (d 1) → F)
    (P₂ : Fin (dS 2) → Fin (d 2) → F) : legTriple P₀ P₁ P₂ 0 = P₀ := rfl

@[simp] lemma legTriple_one {dS d : Fin 3 → ℕ+}
    (P₀ : Fin (dS 0) → Fin (d 0) → F) (P₁ : Fin (dS 1) → Fin (d 1) → F)
    (P₂ : Fin (dS 2) → Fin (d 2) → F) : legTriple P₀ P₁ P₂ 1 = P₁ := rfl

@[simp] lemma legTriple_two {dS d : Fin 3 → ℕ+}
    (P₀ : Fin (dS 0) → Fin (d 0) → F) (P₁ : Fin (dS 1) → Fin (d 1) → F)
    (P₂ : Fin (dS 2) → Fin (d 2) → F) : legTriple P₀ P₁ P₂ 2 = P₂ := rfl

/-- Re-indexing `(∀ i : Fin 3, Fin (d i)) ≃ Fin (d 0) × Fin (d 1) × Fin (d 2)`. -/
def piFin3Equiv {d : Fin 3 → ℕ+} :
    (∀ i : Fin 3, Fin (d i)) ≃ Fin (d 0) × Fin (d 1) × Fin (d 2) where
  toFun g := (g 0, g 1, g 2)
  invFun p := idx3 p.1 p.2.1 p.2.2
  left_inv g := by
    funext i
    fin_cases i <;> rfl
  right_inv p := rfl

lemma sum_pi_fin3 {M : Type*} [AddCommMonoid M] {d : Fin 3 → ℕ+}
    (f : (∀ i : Fin 3, Fin (d i)) → M) :
    (∑ g : ∀ i : Fin 3, Fin (d i), f g)
      = ∑ x : Fin (d 0), ∑ y : Fin (d 1), ∑ z : Fin (d 2), f (idx3 x y z) := by
  classical
  rw [Fintype.sum_equiv (piFin3Equiv (d := d)) f
      (fun p => f (idx3 p.1 p.2.1 p.2.2)) (fun g => by simp [piFin3Equiv])]
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl (fun x _ => Fintype.sum_prod_type _)

end Foundations.HyperbolicLift

namespace Foundations.CornerSquare

open Semicontinuity Foundations.HyperbolicLift

variable {F : Type*} [Field F]

lemma kron_idx3 {d d' : Fin 3 → ℕ+} (S : KTensor F d) (T : KTensor F d')
    (a : Fin ((d 0 * d' 0 : ℕ+) : ℕ)) (b : Fin ((d 1 * d' 1 : ℕ+) : ℕ))
    (x : Fin ((d 2 * d' 2 : ℕ+) : ℕ)) :
    (S ⊠ T) (idx3 (d := fun i => d i * d' i) a b x)
      = S (idx3 (kronDecodeL a) (kronDecodeL b) (kronDecodeL x))
        * T (idx3 (kronDecodeR a) (kronDecodeR b) (kronDecodeR x)) := by
  show S (kronLeftIndex _) * T (kronRightIndex _) = _
  congr 1
  · congr 1; funext i; rw [← kronDecodeL_eq_kronLeftIndex]; fin_cases i <;> rfl
  · congr 1; funext i; rw [← kronDecodeR_eq_kronRightIndex]; fin_cases i <;> rfl

end Foundations.CornerSquare
