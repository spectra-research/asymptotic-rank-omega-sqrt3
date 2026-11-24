import Lib.OM.PolMul.Superadditivity.SA2
import Foundations.Tensors.Semicontinuity.MaxRankBound
import Mathlib.Analysis.Real.Sqrt

/-! # Grouping tensor-power summands by letter multiplicity

Group the words by letter multiplicity in a power of a finite crossing expansion. On each
fiber of `wordType`, both products of cut ranks are constant. This gives a bound
on the geometric mean of the two ranks of the entire fiber sum.
-/

namespace OM.NNN32

open Semicontinuity OM.PolMul.Superadditivity

variable {F : Type*} [Field F] {k : ℕ} {d : Fin k → ℕ+}

theorem matrix_rank_add_le {M N : Type*} [Fintype M] [Fintype N] (A B : Matrix M N F) :
    (A + B).rank ≤ A.rank + B.rank := by
  have hadd := congrArg (fun f : (N → F) →ₗ[F] (M → F) => Module.finrank F (LinearMap.range f))
    (Matrix.mulVecLin_add A B)
  exact hadd.le.trans ((Submodule.finrank_mono (LinearMap.range_add_le A.mulVecLin B.mulVecLin)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _))

/-- Subadditivity of every flattening rank under ordinary finite tensor sums. -/
theorem flatRank_sum_le {ι : Type*} (a : Finset ι) (T : ι → KTensor F d)
    (I : Finset (Fin k)) :
    flatRank (∑ i ∈ a, T i) I ≤ ∑ i ∈ a, flatRank (T i) I := by
  classical
  induction a using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    change (0 : Matrix _ _ F).rank ≤ 0
    exact Matrix.rank_zero.le
  | @insert i a hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    refine le_trans ?_ (Nat.add_le_add_left ih _)
    exact matrix_rank_add_le (flattenMatrix (T i) I) (flattenMatrix (∑ j ∈ a, T j) I)

variable {p m : ℕ}

private theorem prod_by_wordType {A : Type*} [CommMonoid A] (f : Fin m → A)
    (w : Fin p → Fin m) :
    (∏ i, f (w i)) = ∏ j, f j ^ (wordType w j : ℕ) := by
  classical
  simpa only [Finset.prod_const, Finset.card_univ, wordType] using
    (Fintype.prod_fiberwise' w f).symm

/-- On a fixed word type the rank bound for an individual word is constant. -/
theorem flatRank_wordType_sum_le (T : (Fin p → Fin m) → KTensor F d)
    (I : Finset (Fin k)) (r : Fin m → ℕ)
    (hr : ∀ w, flatRank (T w) I ≤ ∏ i, r (w i)) (μ : Fin m → Fin (p + 1)) :
    flatRank (∑ w : {w : Fin p → Fin m // wordType w = μ}, T w.val) I ≤
      Fintype.card {w : Fin p → Fin m // wordType w = μ} * ∏ j, r j ^ (μ j : ℕ) := by
  classical
  refine (flatRank_sum_le Finset.univ _ I).trans ?_
  calc
    _ ≤ ∑ _w : {w : Fin p → Fin m // wordType w = μ}, ∏ j, r j ^ (μ j : ℕ) := by
      apply Finset.sum_le_sum
      intro w _
      exact (hr w.val).trans_eq ((prod_by_wordType r w.val).trans (by rw [w.property]))
    _ = _ := by simp

/-- If each word has product bounds on its two cut ranks, the geometric-mean
cost of any one multiplicity group is at most the single-letter cost to power `p`. -/
theorem sqrt_flatRank_wordType_sum_le (T : (Fin p → Fin m) → KTensor F d)
    (I J : Finset (Fin k)) (r s : Fin m → ℕ)
    (hr : ∀ w, flatRank (T w) I ≤ ∏ i, r (w i))
    (hs : ∀ w, flatRank (T w) J ≤ ∏ i, s (w i)) (μ : Fin m → Fin (p + 1)) :
    let G := ∑ w : {w : Fin p → Fin m // wordType w = μ}, T w.val
    Real.sqrt ((flatRank G I : ℝ) * (flatRank G J : ℝ)) ≤
      (∑ j, Real.sqrt ((r j : ℝ) * (s j : ℝ))) ^ p := by
  classical
  let W := {w : Fin p → Fin m // wordType w = μ}
  let G := ∑ w : W, T w.val
  let a := ∏ j, r j ^ (μ j : ℕ)
  let b := ∏ j, s j ^ (μ j : ℕ)
  let f := fun j => Real.sqrt ((r j : ℝ) * (s j : ℝ))
  change Real.sqrt ((flatRank G I : ℝ) * (flatRank G J : ℝ)) ≤ (∑ j, f j) ^ p
  have hI : (flatRank G I : ℝ) ≤ (Fintype.card W : ℝ) * (a : ℝ) := by
    exact_mod_cast flatRank_wordType_sum_le T I r hr μ
  have hJ : (flatRank G J : ℝ) ≤ (Fintype.card W : ℝ) * (b : ℝ) := by
    exact_mod_cast flatRank_wordType_sum_le T J s hs μ
  have hword (w : W) : Real.sqrt ((a : ℝ) * (b : ℝ)) = ∏ i, f (w.val i) := by
    have ha : (∏ i, r (w.val i)) = a := (prod_by_wordType r w.val).trans (by rw [w.property])
    have hb : (∏ i, s (w.val i)) = b := (prod_by_wordType s w.val).trans (by rw [w.property])
    rw [← ha, ← hb, Nat.cast_prod, Nat.cast_prod, ← Finset.prod_mul_distrib]
    exact Real.sqrt_prod _ fun _ _ => by positivity
  calc
    _ ≤ Real.sqrt (((Fintype.card W : ℝ) * a) * ((Fintype.card W : ℝ) * b)) :=
      Real.sqrt_le_sqrt (mul_le_mul hI hJ (by positivity) (by positivity))
    _ = (Fintype.card W : ℝ) * Real.sqrt ((a : ℝ) * b) := by
      rw [show ((Fintype.card W : ℝ) * a) * ((Fintype.card W : ℝ) * b) =
        (Fintype.card W : ℝ) ^ 2 * ((a : ℝ) * b) by ring,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg _)]
    _ = ∑ _w : W, Real.sqrt ((a : ℝ) * b) := by simp
    _ = ∑ w : W, ∏ i, f (w.val i) := Finset.sum_congr rfl (fun w _ => hword w)
    _ ≤ (∑ j, f j) ^ p := by
      rw [Fintype.sum_pow, ← Fintype.sum_fiberwise wordType]
      apply Finset.single_le_sum (f := fun ν : Fin m → Fin (p + 1) =>
        ∑ w : {w : Fin p → Fin m // wordType w = ν}, ∏ i, f (w.val i)) _ (Finset.mem_univ μ)
      intro ν _
      exact Finset.sum_nonneg fun w _ => Finset.prod_nonneg fun i _ => Real.sqrt_nonneg _

end OM.NNN32

