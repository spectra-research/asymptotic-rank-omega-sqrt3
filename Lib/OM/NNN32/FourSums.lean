import Lib.OM.NNN32.BondFactors

/-! # Ordinary sums at four-party spectral points -/

noncomputable section
open scoped Classical

namespace OM.NNN32

open Semicontinuity AsymptoticSpectrumDuality

/-- On each leg fold the two direct-sum blocks onto their common output. -/
lemma ordinary_add_restricts {d : Fin 4 → ℕ+} (S T : KTensor ℂ d) : Restricts (S+T) (directSumTensor S T) := by
  let lo (i : Fin 4) (a : Fin (d i)) : Fin ((d i+d i : ℕ+) : ℕ) := ⟨a.val,by
    rw [PNat.add_coe]; omega⟩
  let hi (i : Fin 4) (a : Fin (d i)) : Fin ((d i+d i : ℕ+) : ℕ) := ⟨(d i : ℕ)+a.val,by
    rw [PNat.add_coe]; omega⟩
  let A (i : Fin 4) (a : Fin (d i)) (b : Fin ((d i+d i : ℕ+) : ℕ)) : ℂ :=
    if b=lo i a ∨ b=hi i a then 1 else 0
  refine ⟨A,fun x => ?_⟩
  let L := fun i => lo i (x i)
  let H := fun i => hi i (x i)
  have hl (i : Fin 4) : (L i).val < (d i : ℕ) := (x i).isLt
  have hh (i : Fin 4) : (d i : ℕ) ≤ (H i).val := Nat.le_add_right _ _
  have hne : L ≠ H := by
    intro h
    have e := congrArg Fin.val (congrFun h 0)
    have := hl 0
    have := hh 0
    omega
  have term (y : (i : Fin 4) → Fin ((d i+d i : ℕ+) : ℕ)) :
      (∏ i, A i (x i) (y i)) * directSumTensor S T y =
      (if y=L then S x else 0) + (if y=H then T x else 0) := by
    rw [directSumTensor_apply_block']
    by_cases hL : y=L
    · subst y
      simp [A,L,hne,lo,hl]
    by_cases hH : y=H
    · subst y
      have nlow : ¬ ∀ i, (H i).val < (d i : ℕ) := fun h => ((h 0).not_ge (hh 0))
      simp [A,H,hne.symm,hi,hh,nlow]
    simp only [if_neg hL,if_neg hH,add_zero]
    by_cases low : ∀ i, (y i).val < (d i : ℕ)
    · obtain ⟨i,hn⟩ : ∃ i, y i ≠ L i := by by_contra! h; exact hL (funext h)
      have hm : y i ≠ H i := fun he => (low i).not_ge (he ▸ hh i)
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (show A i (x i) (y i) = 0 from if_neg (not_or.2 ⟨hn,hm⟩)),zero_mul]
    by_cases high : ∀ i, (d i : ℕ) ≤ (y i).val
    · obtain ⟨i,hn⟩ : ∃ i, y i ≠ H i := by by_contra! h; exact hH (funext h)
      have hm : y i ≠ L i := fun he => (hl i).not_ge (he ▸ high i)
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (show A i (x i) (y i) = 0 from if_neg (not_or.2 ⟨hm,hn⟩)),zero_mul]
    simp [low,high]
  simp_rw [term,Finset.sum_add_distrib]
  simp

theorem fourValue_add {d : Fin 4 → ℕ+} (φ : AsymptoticSpectrum fourPreorder) (S T : KTensor ℂ d) :
    fourValue φ (S+T) ≤ fourValue φ S + fourValue φ T :=
  (φ.monotone (TensorClass.mk ⟨_,S+T⟩) (TensorClass.mk ⟨_,directSumTensor S T⟩) (ordinary_add_restricts S T)).trans_eq
    (φ.map_add (TensorClass.mk ⟨_,S⟩) (TensorClass.mk ⟨_,T⟩))

@[simp] lemma fourValue_zero {d : Fin 4 → ℕ+} (φ : AsymptoticSpectrum fourPreorder) :
    fourValue φ (0 : KTensor ℂ d) = 0 := by
  have he : TensorClass.mk ⟨_, (0 : KTensor ℂ d)⟩ = (0 : TensorClass ℂ 4) :=
    TensorClass.mk_eq_of_equiv zeroT_equiv_zero.symm
  simp [fourValue,he,AsymptoticSpectrum.eval_zero]

theorem fourValue_sum {d : Fin 4 → ℕ+} (φ : AsymptoticSpectrum fourPreorder)
    {ι : Type} (s : Finset ι) (T : ι → KTensor ℂ d) :
    fourValue φ (∑ i ∈ s, T i) ≤ ∑ i ∈ s, fourValue φ (T i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s h ih =>
    rw [Finset.sum_insert h,Finset.sum_insert h]
    exact (fourValue_add _ _ _).trans (add_le_add le_rfl ih)

end OM.NNN32
