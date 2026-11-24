import Lib.OM.NNN32.Minimum
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-! # The cheaper cut and the partial-transpose splitting cost -/

noncomputable section

namespace OM.NNN32

open Semicontinuity

def splitCosts (D : ℕ+) := {k : ℕ | ∃ R S : Four D,
  R+S = crossing D ∧ k = flatRank R {0,1} + flatRank S {0,2}}

lemma split_min (D : ℕ+) : IsLeast (splitCosts D) (P D) :=
  isLeast_csInf ⟨_,crossing D,0,add_zero _,rfl⟩

lemma cheaper_le_weight {D : ℕ+} (T : Four D) :
    ((min (flatRank T {0,1}) (flatRank T {0,2}) : ℕ) : ℝ) ≤ weight T := by
  apply Real.le_sqrt_of_sq_le
  rw [sq]
  exact_mod_cast Nat.mul_le_mul (min_le_left _ _) (min_le_right _ _)

lemma P_le_cost {D : ℕ+} {c : ℝ} (hc : c ∈ expansionCosts (crossing D)) : (P D : ℝ) ≤ c := by
  classical
  obtain ⟨m,B,hB,rfl⟩ := hc
  let r j := flatRank (B j) {0,1}
  let s j := flatRank (B j) {0,2}
  let p j := r j ≤ s j
  let I := Finset.univ.filter p
  let J := Finset.univ.filter (fun j => ¬ p j)
  have add {A : Type} [AddCommMonoid A] (f : Fin m → A) :
      (∑ j ∈ I, f j) + (∑ j ∈ J, f j) = ∑ j, f j :=
    Finset.sum_filter_add_sum_filter_not Finset.univ p f
  have hmin := (split_min D).2 (show _ ∈ splitCosts D from
    ⟨∑ j ∈ I, B j, ∑ j ∈ J, B j, (add B).trans hB, rfl⟩)
  have hnat : P D ≤ ∑ j, min (r j) (s j) := by
    refine (hmin.trans (Nat.add_le_add (flatRank_sum_le I B _) (flatRank_sum_le J B _))).trans_eq ?_
    rw [← add (fun j => min (r j) (s j))]
    congr 1
    · exact Finset.sum_congr rfl fun j hj => (min_eq_left (Finset.mem_filter.mp hj).2).symm
    · exact Finset.sum_congr rfl fun j hj =>
        (min_eq_right (le_of_not_ge (Finset.mem_filter.mp hj).2)).symm
  calc
    (P D : ℝ) ≤ ((∑ j, min (r j) (s j) : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = ∑ j, ((min (r j) (s j) : ℕ) : ℝ) := Nat.cast_sum _ _
    _ ≤ _ := Finset.sum_le_sum fun j _ => cheaper_le_weight (B j)

private def slice {D : ℕ+} (T : Four D) : Matrix (Index D) (Index D) ℂ :=
  fun i j => coeff T ⟨0,D.2⟩ i j ⟨0,D.2⟩

theorem size_le_P (D : ℕ+) : (D : ℕ) ≤ P D := by
  classical
  obtain ⟨R,S,h,hcost⟩ := (split_min D).1
  have he : slice R + slice S = (1 : Matrix (Index D) (Index D) ℂ) := by
    funext i j
    have hh := congrFun h ![⟨0,D.2⟩,i,j,⟨0,D.2⟩]
    simpa [slice,coeff,crossing,matching,Matrix.one_apply] using hh
  have hr := (rowMatrix R).rank_submatrix_le (fun i => (⟨0,D.2⟩,i)) (fun j => (j,⟨0,D.2⟩))
  have hs := (colMatrix S).rank_submatrix_le (fun i => (⟨0,D.2⟩,i)) (fun j => (j,⟨0,D.2⟩))
  change (slice R).rank ≤ _ at hr
  change (slice S).transpose.rank ≤ _ at hs
  rw [Matrix.rank_transpose,colMatrix_rank] at hs
  rw [rowMatrix_rank] at hr
  have hall := (matrix_rank_add_le (slice R) (slice S)).trans (Nat.add_le_add hr hs)
  rw [he,Matrix.rank_one,Fintype.card_fin,← hcost] at hall
  exact hall

lemma size_le_W (D : ℕ+) : ((D : ℕ) : ℝ) ≤ W D :=
  (show ((D : ℕ) : ℝ) ≤ P D by exact_mod_cast size_le_P D).trans (P_le_cost (expansion_isLeast _).1)

end OM.NNN32
