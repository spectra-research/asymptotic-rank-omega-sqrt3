import Lib.OM.NNN32.Cuts
import PLATFORM.Statements.«R113.13»

/-! # The infimum of expansion costs is attained -/

noncomputable section

namespace OM.NNN32

open Semicontinuity

lemma weight_mem_costs {d : Fin 4 → ℕ+} (T : KTensor ℂ d) : weight T ∈ expansionCosts T :=
  ⟨1,fun _ => T,by simp,by simp [weight]⟩

/-- Under a cost cap, each nonzero radical is a square root of a bounded natural
number and its multiplicity is bounded. Zero summands do not affect the cost. -/
lemma finite_costs_below {d : Fin 4 → ℕ+} (T : KTensor ℂ d) (C : ℝ) :
    (expansionCosts T ∩ Set.Iic C).Finite := by
  classical
  let I := Fin (⌊C^2⌋₊+1)
  let J := Fin (⌊C⌋₊+1)
  let cost (μ : I → J) := ∑ i, ((μ i : ℕ) : ℝ)*Real.sqrt (i : ℕ)
  apply (Set.finite_range cost).subset
  rintro s ⟨⟨m,B,_,hs⟩,hC⟩
  change s = ∑ j, weight (B j) at hs
  change s ≤ C at hC
  let n j := flatRank (B j) {0,1} * flatRank (B j) {0,2}
  have radical j : weight (B j) = Real.sqrt (n j : ℕ) := by simp [n,weight]
  have hw j : weight (B j) ≤ C :=
    (Finset.single_le_sum (f := fun j => weight (B j)) (fun _ _ => Real.sqrt_nonneg _)
      (Finset.mem_univ j)).trans (hs ▸ hC)
  have hn j : n j ≤ ⌊C^2⌋₊ := by
    apply Nat.le_floor
    have hh := pow_le_pow_left₀ (Real.sqrt_nonneg _) (hw j) 2
    change weight (B j)^2 ≤ C^2 at hh
    rwa [radical, Real.sq_sqrt (Nat.cast_nonneg _)] at hh
  let t (j : Fin m) : I := ⟨n j,Nat.lt_succ_of_le (hn j)⟩
  let count (i : I) := Fintype.card {j // t j = i}
  let term (i : I) : ℝ := (count i : ℝ)*Real.sqrt (i : ℕ)
  have hcount : s = ∑ i, term i := by
    rw [hs,← Fintype.sum_fiberwise t]
    apply Finset.sum_congr rfl
    intro i _
    have hi (j : {j // t j = i}) : weight (B j.1) = Real.sqrt (i : ℕ) :=
      (radical j.1).trans (congrArg (fun k : I => Real.sqrt (k : ℕ)) j.2)
    simp [hi,term,count]
  have bound (i : I) (hi : i.val ≠ 0) : count i ≤ ⌊C⌋₊ := by
    have h1 : 1 ≤ Real.sqrt (i : ℕ) := by
      simpa using Real.sqrt_le_sqrt (by exact_mod_cast Nat.one_le_iff_ne_zero.2 hi : (1:ℝ) ≤ i.val)
    apply Nat.le_floor
    calc
      _ ≤ term i := le_mul_of_one_le_right (Nat.cast_nonneg _) h1
      _ ≤ ∑ j, term j := Finset.single_le_sum (f := term) (fun j _ =>
        mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)) (Finset.mem_univ i)
      _ ≤ C := hcount ▸ hC
  let μ (i : I) : J := if h : i.val = 0 then ⟨0,Nat.succ_pos _⟩
    else ⟨count i,Nat.lt_succ_of_le (bound i h)⟩
  refine ⟨μ, hcount ▸ Finset.sum_congr rfl (fun i _ => ?_)⟩
  by_cases hi : i.val = 0
  · simp [μ,term,hi]
  · simp only [μ,term,dif_neg hi]

theorem expansion_isLeast {d : Fin 4 → ℕ+} (T : KTensor ℂ d) :
    IsLeast (expansionCosts T) (sInf (expansionCosts T)) := by
  classical
  let s := (finite_costs_below T (weight T)).toFinset
  have hmem (x : ℝ) : x ∈ s ↔ x ∈ expansionCosts T ∧ x ≤ weight T := Set.Finite.mem_toFinset _
  have ht : weight T ∈ s := (hmem _).2 ⟨weight_mem_costs T,le_rfl⟩
  have hn : s.Nonempty := ⟨_,ht⟩
  have hm := (hmem _).1 (s.min'_mem hn)
  have h : IsLeast (expansionCosts T) (s.min' hn) := by
    refine ⟨hm.1,fun x hx => ?_⟩
    by_cases hxt : x ≤ weight T
    · exact s.min'_le x ((hmem _).2 ⟨hx,hxt⟩)
    · exact hm.2.trans (le_of_not_ge hxt)
  rwa [h.csInf_eq]

theorem proof_R113_13 : S_R113_13 := fun D => expansion_isLeast (crossing D)

end OM.NNN32
