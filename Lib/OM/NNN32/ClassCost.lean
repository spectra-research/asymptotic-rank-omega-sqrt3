import Lib.OM.NNN32.Growth

/-! # Expansion cost under restriction, direct sums and Kronecker products -/

noncomputable section

namespace OM.NNN32

open Semicontinuity

lemma tensorCost_mono {d e : Fin 4 → ℕ+} {S : KTensor ℂ d} {T : KTensor ℂ e}
    (h : Restricts S T) : tensorCost S ≤ tensorCost T := by
  classical
  obtain ⟨A,hA⟩ := h
  obtain ⟨m,B,hB,hc⟩ := (expansion_isLeast T).1
  let C (j : Fin m) : KTensor ℂ d := fun x => ∑ y, (∏ i, A i (x i) (y i)) * B j y
  have hs : S = ∑ j, C j := by
    funext x
    rw [hA,← hB,Finset.sum_apply]
    simp only [Finset.sum_apply,Finset.mul_sum,C]
    rw [Finset.sum_comm]
  change tensorCost T = ∑ j, weight (B j) at hc
  rw [hs,hc]
  apply (cost_le_sum C).trans
  apply Finset.sum_le_sum
  intro j _
  have hr : Restricts (C j) (B j) := ⟨A,fun _ => rfl⟩
  apply Real.sqrt_le_sqrt
  exact_mod_cast Nat.mul_le_mul (hr.flatRank_le {0,1}) (hr.flatRank_le {0,2})

lemma tensorCost_add {d : Fin 4 → ℕ+} (S T : KTensor ℂ d) :
    tensorCost (S + T) ≤ tensorCost S + tensorCost T := by
  classical
  obtain ⟨m,A,hA,ha⟩ := (expansion_isLeast S).1
  obtain ⟨n,B,hB,hb⟩ := (expansion_isLeast T).1
  change tensorCost S = ∑ i, weight (A i) at ha
  change tensorCost T = ∑ i, weight (B i) at hb
  simpa [Fintype.sum_sum_type,hA,hB,ha,hb] using cost_le_sum (Sum.elim A B)

lemma tensorCost_kron {d e : Fin 4 → ℕ+} (S : KTensor ℂ d) (T : KTensor ℂ e) :
    tensorCost (kroneckerTensor S T) ≤ tensorCost S * tensorCost T := by
  classical
  obtain ⟨m,A,hA,ha⟩ := (expansion_isLeast S).1
  obtain ⟨n,B,hB,hb⟩ := (expansion_isLeast T).1
  let C (p : Fin m × Fin n) := kroneckerTensor (A p.1) (B p.2)
  have hs : ∑ p, C p = kroneckerTensor S T := by
    funext x
    simp [← hA,← hB,C,kroneckerTensor,Fintype.sum_prod_type,Finset.sum_mul,Finset.mul_sum]
    exact Finset.sum_comm
  change tensorCost S = ∑ j, weight (A j) at ha
  change tensorCost T = ∑ j, weight (B j) at hb
  rw [← hs,ha,hb]
  calc
    _ ≤ _ := cost_le_sum C
    _ ≤ ∑ p : Fin m × Fin n, weight (A p.1) * weight (B p.2) :=
      Finset.sum_le_sum fun p _ => weight_kron _ _
    _ = _ := by
      simp [Fintype.sum_prod_type,Finset.sum_mul,Finset.mul_sum]
      exact Finset.sum_comm

def classCost : TensorClass ℂ 4 → ℝ :=
  Quotient.lift (fun T : TT ℂ 4 => tensorCost T.2) fun _ _ h =>
    le_antisymm (tensorCost_mono h.1) (tensorCost_mono h.2)

lemma classCost_nonneg (x : TensorClass ℂ 4) : 0 ≤ classCost x := by
  induction x using Quotient.inductionOn with
  | _ a =>
    obtain ⟨m,B,_,hc⟩ := (expansion_isLeast a.2).1
    change sInf _ = ∑ j, weight (B j) at hc
    change 0 ≤ sInf _
    rw [hc]
    exact Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _

lemma classCost_mono (x y : TensorClass ℂ 4) (h : relClass x y) : classCost x ≤ classCost y := by
  induction x,y using Quotient.inductionOn₂ with
  | _ a b => exact tensorCost_mono h

lemma classCost_mul (x y : TensorClass ℂ 4) : classCost (x*y) ≤ classCost x * classCost y := by
  induction x,y using Quotient.inductionOn₂ with
  | _ a b => exact tensorCost_kron a.2 b.2

lemma classCost_add (x y : TensorClass ℂ 4) : classCost (x+y) ≤ classCost x + classCost y := by
  induction x,y using Quotient.inductionOn₂ with
  | _ a b =>
    obtain ⟨d,S⟩ := a
    obtain ⟨e,T⟩ := b
    let S' := directSumTensor S (0 : KTensor ℂ e)
    let T' := directSumTensor (0 : KTensor ℂ d) T
    have he : directSumTensor S T = S' + T' := by
      funext z
      simp only [S',T',Pi.add_apply,directSumTensor_apply_block']
      split_ifs <;> simp
    change tensorCost (directSumTensor S T) ≤ tensorCost S + tensorCost T
    rw [he]
    exact (tensorCost_add S' T').trans (add_le_add
      (tensorCost_mono ((directSum_comm S (0 : KTensor ℂ e)).1.trans (zero_directSum_restricts S)))
      (tensorCost_mono (zero_directSum_restricts T)))

private lemma flatRank_one_le (I : Finset (Fin 4)) : flatRank (unitTensor ℂ 1) I ≤ 1 := by
  classical
  apply (Matrix.rank_le_card_width _).trans
  simp

lemma classCost_one : classCost 1 ≤ 1 := by
  apply ((expansion_isLeast _).2 (weight_mem_costs (unitTensor ℂ (k := 4) 1))).trans
  apply (Real.sqrt_le_iff).2
  constructor
  · norm_num
  · norm_num
    exact_mod_cast (Nat.mul_le_mul (flatRank_one_le {0,1}) (flatRank_one_le {0,2}))

lemma classCost_nat (n : ℕ) : classCost n ≤ n := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero]
    change tensorCost (0 : Four 1) ≤ 0
    exact ((expansion_isLeast _).2 (weight_mem_costs _)).trans_eq (weight_zero _)
  | succ n ih =>
    push_cast
    exact (classCost_add _ _).trans (add_le_add ih classCost_one)

lemma classCost_pow (x : TensorClass ℂ 4) (n : ℕ) : classCost (x^n) ≤ classCost x ^ n := by
  induction n with
  | zero => simpa using classCost_one
  | succ n ih =>
    rw [pow_succ,pow_succ]
    exact (classCost_mul _ _).trans (mul_le_mul_of_nonneg_right ih (classCost_nonneg x))

end OM.NNN32
