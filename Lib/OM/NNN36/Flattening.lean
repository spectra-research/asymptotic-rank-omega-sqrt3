import Foundations.Tensors.Coordinates
import Foundations.Tensors.Semicontinuity.ZariskiSublevel

/-! # Tensor slices and full-rank third flattenings -/

namespace OM.NNN36

open Semicontinuity Foundations.HyperbolicLift

variable {F : Type*} [Field F] {d : Fin 3 → ℕ+}

/-- Each pair of first and second indices gives one simple summand. -/
theorem tensorRank_le_first_two (T : KTensor F d) :
    tensorRank T ≤ (d 0 : ℕ) * (d 1 : ℕ) := by
  classical
  let factors (p : Fin (d 0) × Fin (d 1)) : (i : Fin 3) → Fin (d i) → F :=
    Fin.cases (fun a => if a = p.1 then 1 else 0)
      (Fin.cases (fun b => if b = p.2 then 1 else 0)
        (Fin.cases (fun c => T (idx3 p.1 p.2 c)) (fun i => i.elim0)))
  apply Nat.sInf_le
  refine ⟨fun j => simpleTensor (factors (finProdFinEquiv.symm j)), fun _ => ⟨_, rfl⟩, ?_⟩
  funext idx
  have entry (p : Fin (d 0) × Fin (d 1)) :
      simpleTensor (factors p) idx =
        (if idx 0 = p.1 then 1 else 0) * (if idx 1 = p.2 then 1 else 0) *
          T (idx3 p.1 p.2 (idx 2)) := by
    rw [simpleTensor, Fin.prod_univ_three]
    rfl
  rw [Finset.sum_apply, ← Equiv.sum_comp finProdFinEquiv]
  simp only [Equiv.symm_apply_apply, entry]
  rw [Finset.sum_eq_single (idx 0, idx 1)]
  · simp
  · rintro ⟨a, b⟩ _ hne
    by_cases h : idx 0 = a
    · have h' : idx 1 ≠ b := fun e => hne (Prod.ext h.symm e.symm)
      simp [h']
    · simp [h]
  · simp

/-- Match distinct pairs on the first two legs with distinct third indices.
The selected rows and columns of the third flattening form an identity matrix. -/
theorem exists_third_flatRank_ge (r : ℕ)
    (hp : r ≤ (d 0 : ℕ) * (d 1 : ℕ)) (ht : r ≤ (d 2 : ℕ)) :
    ∃ T : KTensor F d, r ≤ flatRank T {2} := by
  classical
  let pair (v : Fin r) : Fin (d 0) × Fin (d 1) := finProdFinEquiv.symm (Fin.castLE hp v)
  let T : KTensor F d := fun x =>
    if (x 2).val = (finProdFinEquiv (x 0, x 1)).val then 1 else 0
  let cut : Finset (Fin 3) := {2}
  let row (v : Fin r) (i : {i // i ∈ cut}) :=
    idx3 (d := d) ⟨0, (d 0).pos⟩ ⟨0, (d 1).pos⟩ (Fin.castLE ht v) i.val
  let col (v : Fin r) (i : {i // i ∉ cut}) :=
    idx3 (d := d) (pair v).1 (pair v).2 ⟨0, (d 2).pos⟩ i.val
  have hsub : (flattenMatrix T cut).submatrix row col = (1 : Matrix (Fin r) (Fin r) F) := by
    ext i j
    rw [Matrix.submatrix_apply, Matrix.one_apply]
    change (if i.val = (finProdFinEquiv ((pair j).1, (pair j).2)).val then 1 else 0) = _
    rw [Prod.mk.eta, show finProdFinEquiv (pair j) = Fin.castLE hp j from
      finProdFinEquiv.apply_symm_apply _]
    simp [Fin.ext_iff]
  have h := Matrix.rank_submatrix_le (flattenMatrix T cut) row col
  rw [hsub, Matrix.rank_one, Fintype.card_fin] at h
  exact ⟨T, h⟩

end OM.NNN36

