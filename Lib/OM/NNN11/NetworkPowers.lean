import Lib.OM.NNN11.Network

/-! Ordered products and their exact spectral values. Reindexing copy labels
does not permute the three tensor parties. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN11.Network
open CoordinateTensor OM.NNN.Raw OM.NNN2 OM.NNN3
set_option maxHeartbeats 1000000

variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]

def splitFirst (n : ℕ) (E : Type) : (Fin (n + 1) → E) ≃ E × (Fin n → E) where
  toFun x := (x 0, fun i => x i.succ)
  invFun x := Fin.cons x.1 x.2
  left_inv x := by funext i; exact Fin.cases rfl (fun _ => rfl) i
  right_inv x := rfl

theorem value_ordered_fin [Nonempty X] [Nonempty Y] [Nonempty Z]
    (φ : PolMul.Spectral ℂ) (T : Tensor ℂ X Y Z) (n : ℕ) :
    value φ (ordered (D := Fin n) T) = value φ T ^ n := by
  induction n with
  | zero =>
    letI : Unique (Unit × Unit) := ⟨⟨((), ())⟩, fun _ => Subsingleton.elim _ _⟩
    have h := value_reindex φ (mm Unit Unit Unit)
      (Equiv.ofUnique (Fin 0 → X) (Unit × Unit))
      (Equiv.ofUnique (Fin 0 → Y) (Unit × Unit))
      (Equiv.ofUnique (Fin 0 → Z) (Unit × Unit))
    have he : (fun x y z => mm Unit Unit Unit
        (Equiv.ofUnique (Fin 0 → X) (Unit × Unit) x)
        (Equiv.ofUnique (Fin 0 → Y) (Unit × Unit) y)
        (Equiv.ofUnique (Fin 0 → Z) (Unit × Unit) z)) = ordered (D := Fin 0) T := by
      funext x y z
      simp [mm, ordered]
    rw [he, value_mm φ (n := 1) (p := 1) (m := 1)
      (Equiv.ofUnique (Fin 1) Unit) (Equiv.ofUnique (Fin 1) Unit)
      (Equiv.ofUnique (Fin 1) Unit)] at h
    simpa using! h
  | succ n ih =>
    have h := value_reindex φ (tensorProduct T (ordered (D := Fin n) T))
      (splitFirst n X) (splitFirst n Y) (splitFirst n Z)
    have he : (fun x y z => tensorProduct T (ordered (D := Fin n) T)
        (splitFirst n X x) (splitFirst n Y y) (splitFirst n Z z)) =
        ordered (D := Fin (n + 1)) T := by
      funext x y z
      simp [tensorProduct, ordered, splitFirst, Fin.prod_univ_succ]
    rw [he, value_product', ih] at h
    simpa [pow_succ, mul_comm] using! h

theorem value_ordered {D : Type} [Fintype D] [DecidableEq D]
    [Nonempty X] [Nonempty Y] [Nonempty Z]
    (φ : PolMul.Spectral ℂ) (T : Tensor ℂ X Y Z) :
    value φ (ordered (D := D) T) = value φ T ^ Fintype.card D := by
  let e := Fintype.equivFin D
  have h := value_reindex φ (ordered (D := D) T)
    (e.symm.arrowCongr (Equiv.refl X))
    (e.symm.arrowCongr (Equiv.refl Y))
    (e.symm.arrowCongr (Equiv.refl Z))
  have he : (fun x y z => ordered (D := D) T
      (e.symm.arrowCongr (Equiv.refl X) x)
      (e.symm.arrowCongr (Equiv.refl Y) y)
      (e.symm.arrowCongr (Equiv.refl Z) z)) = ordered (D := Fin (Fintype.card D)) T := by
    funext x y z
    exact e.prod_comp (fun d => T (x d) (y d) (z d))
  rw [he, value_ordered_fin] at h
  exact h.symm

def assembleEquiv (A B C E : Type) : Outputs A B C E ≃ (A ⊕ B ⊕ C → E) :=
  (Equiv.prodCongr (Equiv.refl _) (Equiv.sumArrowEquivProdArrow B C E).symm).trans
    (Equiv.sumArrowEquivProdArrow A (B ⊕ C) E).symm

theorem value_contract_identity {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [Nonempty X] [Nonempty Y] [Nonempty Z]
    (φ : PolMul.Spectral ℂ) (T : Tensor ℂ X Y Z) :
    value φ (contract (A := A) (B := B) (C := C)
      T (identity _) (identity _) (identity _)) =
      value φ T ^ (Fintype.card A + Fintype.card B + Fintype.card C) := by
  rw [contract_identity_ordered]
  have h := value_reindex φ (ordered (D := A ⊕ B ⊕ C) T)
    (assembleEquiv A B C X) (assembleEquiv A B C Y) (assembleEquiv A B C Z)
  exact h.trans (by simpa only [Fintype.card_sum, Nat.add_assoc] using!
    (value_ordered (D := A ⊕ B ⊕ C) φ T))

theorem value_contract70_identity [Nonempty X] [Nonempty Y] [Nonempty Z]
    (φ : PolMul.Spectral ℂ) (T : Tensor ℂ X Y Z) :
    value φ (contract (A := Fin 21) (B := Fin 21) (C := Fin 28)
      T (identity _) (identity _) (identity _)) = value φ T ^ 70 := by
  have h := value_contract_identity (A := Fin 21) (B := Fin 21) (C := Fin 28) φ T
  simp only [Fintype.card_fin] at h
  exact h

end OM.NNN11.Network
