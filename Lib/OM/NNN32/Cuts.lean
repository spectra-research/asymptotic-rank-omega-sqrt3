import Lib.OM.NNN32.PowerRestriction

/-! # Product-index matrices for the two crossing cuts -/

namespace OM.NNN32

open Semicontinuity

variable {D : ℕ+}
abbrev Four (D : ℕ+) := KTensor ℂ (fun _ : Fin 4 => D)
abbrev Index (D : ℕ+) := Fin (D : ℕ)

def coeff (T : Four D) (x y u v : Index D) : ℂ := T ![x,y,u,v]

def rowMatrix (T : Four D) : Matrix (Index D × Index D) (Index D × Index D) ℂ :=
  fun a b => coeff T a.1 a.2 b.1 b.2

def colMatrix (T : Four D) : Matrix (Index D × Index D) (Index D × Index D) ℂ :=
  fun a b => coeff T a.1 b.1 a.2 b.2

private def coords (I : Finset (Fin 4)) (i j : Fin 4) (hi : i ∈ I) (hj : j ∈ I)
    (hne : i ≠ j) (hall : ∀ k ∈ I, k = i ∨ k = j) :
    (Index D × Index D) ≃ ({k // k ∈ I} → Index D) where
  toFun a k := if k.val = i then a.1 else a.2
  invFun f := (f ⟨i,hi⟩,f ⟨j,hj⟩)
  left_inv a := by simp [hne.symm]
  right_inv f := by
    funext k
    rcases k with ⟨k,hk⟩
    rcases hall k hk with rfl | rfl <;> simp [hne.symm]

theorem rowMatrix_rank (T : Four D) : (rowMatrix T).rank = flatRank T {0,1} := by
  let I : Finset (Fin 4) := {0,1}
  let r := coords (D := D) I 0 1 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  let s := coords (D := D) Iᶜ 2 3 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  let e : ({i // i ∈ Iᶜ} → Index D) ≃ ({i // i ∉ I} → Index D) :=
    Equiv.arrowCongr (Equiv.subtypeEquivRight (fun i => Finset.mem_compl)) (Equiv.refl _)
  have he : rowMatrix T = (flattenMatrix T I).submatrix r (s.trans e) := by
    funext x y
    apply congrArg T
    funext i
    fin_cases i <;> rfl
  rw [he,Matrix.rank_submatrix]
  rfl

theorem colMatrix_rank (T : Four D) : (colMatrix T).rank = flatRank T {0,2} := by
  let I : Finset (Fin 4) := {0,2}
  let r := coords (D := D) I 0 2 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  let s := coords (D := D) Iᶜ 1 3 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  let e : ({i // i ∈ Iᶜ} → Index D) ≃ ({i // i ∉ I} → Index D) :=
    Equiv.arrowCongr (Equiv.subtypeEquivRight (fun i => Finset.mem_compl)) (Equiv.refl _)
  have he : colMatrix T = (flattenMatrix T I).submatrix r (s.trans e) := by
    funext x y
    apply congrArg T
    funext i
    fin_cases i <;> rfl
  rw [he,Matrix.rank_submatrix]
  rfl

end OM.NNN32
