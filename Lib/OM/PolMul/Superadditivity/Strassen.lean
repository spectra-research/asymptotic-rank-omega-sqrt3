/- Adapted from PolMul/Superadditivity/Strassen.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMul.Superadditivity.Binary

/-! # The Strassen tensor used in the laser bound

The third-leg distinguished coordinate is placed last, so the two blocks are
literally in the order of the project's binary shared-leg sum.
-/

namespace OM.PolMul.Superadditivity

open AsymptoticSpectrumDuality Semicontinuity
open scoped BigOperators

universe u
variable {F : Type u} [Field F]

noncomputable def leftPair (q : ℕ+) : T3 F (fmt q 1 q) :=
  fun x => if (x 0).val = (x 2).val then 1 else 0

noncomputable def rightPair (q : ℕ+) : T3 F (fmt q q 1) :=
  fun x => if (x 0).val = (x 1).val then 1 else 0

lemma matMul_n11_entry (q : ℕ+)
    (x : ∀ i, Fin (fmt (q * 1) (1 * 1) (1 * q) i)) :
    matMul (F := F) q 1 1 x = if (x 0).val = (x 2).val then 1 else 0 := by
  have hx1 : (x 1).val = 0 := by
    have hb : (x 1).val < 1 := (x 1).isLt
    omega
  have hx2 : (x 2).val < (q : ℕ) := by simpa [fmt] using! (x 2).isLt
  simp only [matMul, finProdFinEquiv_symm_apply, Fin.ext_iff,
    Fin.coe_divNat, Fin.coe_modNat, PNat.val_ofNat, Nat.div_one, Nat.mod_one,
    hx1, Nat.div_eq_of_lt hx2, Nat.mod_eq_of_lt hx2]
  simp [eq_comm]

lemma matMul_1n1_entry (q : ℕ+)
    (x : ∀ i, Fin (fmt (1 * q) (q * 1) (1 * 1) i)) :
    matMul (F := F) 1 q 1 x = if (x 0).val = (x 1).val then 1 else 0 := by
  have hx2 : (x 2).val = 0 := by
    have hb : (x 2).val < 1 := (x 2).isLt
    omega
  have hx0 : (x 0).val < (q : ℕ) := by simpa [fmt] using! (x 0).isLt
  simp only [matMul, finProdFinEquiv_symm_apply, Fin.ext_iff,
    Fin.coe_divNat, Fin.coe_modNat, PNat.val_ofNat, Nat.div_one, Nat.mod_one,
    hx2, Nat.div_eq_of_lt hx0, Nat.mod_eq_of_lt hx0]
  simp

lemma leftPair_iso (q : ℕ+) : Iso (leftPair (F := F) q) (matMul q 1 1) := by
  apply iso_of_coordinates _ _ (fun i => finCongr (by fin_cases i <;> simp [fmt]))
  intro x
  rw [matMul_n11_entry]
  rfl

lemma rightPair_iso (q : ℕ+) : Iso (rightPair (F := F) q) (matMul 1 q 1) := by
  apply iso_of_coordinates _ _ (fun i => finCongr (by fin_cases i <;> simp [fmt]))
  intro x
  rw [matMul_1n1_entry]
  rfl

noncomputable def strassenTensor (q : ℕ+) :=
  pdsum (leftPair (F := F) q) (rightPair (F := F) q) rfl

lemma strassenTensor_entry (q : ℕ+)
    (x : ∀ i, Fin (fmt q (1 + q) (q + 1) i)) :
    strassenTensor (F := F) q x =
      (if (x 1).val = 0 then (1 : F) else 0) *
        (if (x 2).val = (x 0).val then 1 else 0) +
      (if (x 1).val = (x 0).val + 1 then 1 else 0) *
        (if (x 2).val = (q : ℕ) then 1 else 0) := by
  have hx0 := (x 0).isLt
  have hx1 := (x 1).isLt
  have hx2 := (x 2).isLt
  simp only [fmt, PNat.add_coe, PNat.val_ofNat] at hx0 hx1 hx2
  change (if (x 1).val < 1 then
    if (x 2).val < (q : ℕ) then (if (x 0).val = (x 2).val then 1 else 0) else 0
    else if (q : ℕ) ≤ (x 2).val then (if (x 0).val = (x 1).val - 1 then 1 else 0)
    else 0) = _
  split_ifs <;> simp only [one_mul, zero_mul, add_zero, zero_add] <;> first | rfl | omega

lemma C_indicator (P : Prop) [Decidable P] :
    Polynomial.C (if P then (1 : F) else 0) = (if P then (1 : Polynomial F) else 0) := by
  split_ifs <;> simp

-- The sparse polynomial contraction has only two nonzero diagonal columns.
set_option maxHeartbeats 400000 in
lemma strassenTensor_degen (q : ℕ+) :
    Degen (strassenTensor (F := F) q) (unitTensor F (k := 3) (q + 1)) := by
  classical
  let A : ∀ i : Fin 3, Matrix (Fin (fmt q (1 + q) (q + 1) i)) (Fin (q + 1 : ℕ+))
      (Polynomial F)
    | 0 => fun x c => (if c.val = x.val + 1 then 1 else 0) - (if c.val = 0 then 1 else 0)
    | 1 => fun x c => (if x.val = 0 then 1 else 0) + Polynomial.X * (if x.val = c.val then 1 else 0)
    | 2 => fun x c => (if x.val = (q : ℕ) then 1 else 0) + Polynomial.X * (if x.val + 1 = c.val then 1 else 0)
  -- Column zero is the subtracting rank-one term, with no epsilon correction.
  let B : ∀ i : Fin 3, Matrix (Fin (fmt q (1 + q) (q + 1) i)) (Fin (q + 1 : ℕ+))
      (Polynomial F) := fun i x c => if c.val = 0 ∧ i ≠ 0 then
        (if i = 1 then (if x.val = 0 then 1 else 0) else (if x.val = (q : ℕ) then 1 else 0))
      else A i x c
  apply DegenerationFacts.degen_of_arc
  refine ⟨1, B, fun x => Polynomial.C
    ((if (x 1).val = (x 0).val + 1 then (1 : F) else 0) *
      (if (x 2).val = (x 0).val then 1 else 0)), ?_⟩
  intro x
  let c : Fin (q + 1 : ℕ+) := ⟨(x 0).val + 1, by
    have hx : (x 0).val < (q : ℕ) := (x 0).isLt
    change (x 0).val + 1 < (q : ℕ) + 1
    omega⟩
  have hc : c ≠ 0 := by intro hh; have := congrArg Fin.val hh; simp [c] at this
  have hdiag : DegenerationFacts.action B
      (DegenerationFacts.constTensor (unitTensor F (k := 3) (q + 1))) x =
      ∑ j : Fin (q + 1 : ℕ+), ∏ i : Fin 3, B i (x i) j := by
    unfold DegenerationFacts.action DegenerationFacts.constTensor
    simp only [unitTensor, C_indicator, mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter]
    refine Finset.sum_bij (fun y _ => y 0) ?_ ?_ ?_ ?_
    · intro y hy
      exact Finset.mem_univ _
    · intro a ha b hb hab
      have ha' := (Finset.mem_filter.mp ha).2
      have hb' := (Finset.mem_filter.mp hb).2
      funext i
      exact (ha' i 0).trans (hab.trans (hb' i 0).symm)
    · intro j _
      exact ⟨fun _ => j, by simp, rfl⟩
    · intro y hy
      have hy' := (Finset.mem_filter.mp hy).2
      congr 1
      funext i
      exact congrArg (B i (x i)) (hy' i 0)
  rw [hdiag]
  have hsum : (∑ j : Fin (q + 1 : ℕ+), ∏ i : Fin 3, B i (x i) j) =
      (∏ i : Fin 3, B i (x i) c) + (∏ i : Fin 3, B i (x i) 0) := by
    rw [← Finset.sum_subset (Finset.subset_univ ({c, 0} : Finset _))]
    · simp [hc]
    · intro j _ hj
      have hjc : j ≠ c := by intro he; subst j; simp at hj
      have hj0 : j ≠ 0 := by intro he; subst j; simp at hj
      apply Finset.prod_eq_zero (Finset.mem_univ 0)
      have hjcv : j.val ≠ (x 0).val + 1 := fun h => hjc (Fin.ext h)
      have hj0v : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
      simp [B, A, hjcv, hj0v, hj0]
  rw [hsum, strassenTensor_entry]
  have hcv : c.val ≠ 0 := by simp [c]
  norm_num only [Fin.prod_univ_three, B, A, c, Fin.val_zero, Fin.isValue,
    Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, and_true,
    if_false, if_true, sub_zero, zero_sub, one_mul, neg_mul, zero_mul,
    Nat.add_right_cancel_iff]
  simp only [map_add, map_mul, C_indicator, pow_one]
  simp [Nat.add_comm, show ¬ (0 = 1 + (x 0).val) by omega]
  split_ifs <;> ring


lemma eval_strassenTensor_le (φ : Spectral F) (q : ℕ+) :
    Spectral.eval φ (strassenTensor (F := F) q) ≤ ((q : ℕ) : ℝ) + 1 := by
  have H := SpectralFacts.proof_SP_2 F φ _ _ (strassenTensor_degen (F := F) q)
  change Spectral.eval φ (strassenTensor (F := F) q) ≤
    Spectral.eval φ (unitTensor F (k := 3) (q + 1)) at H
  have hu : Spectral.eval φ (unitTensor F (k := 3) (q + 1)) = (((q + 1 : ℕ+) : ℕ) : ℝ) := by
    change AsymptoticSpectrum.eval _ (TensorClass.mk ⟨_, unitTensor F (k := 3) (q + 1)⟩) φ = _
    rw [DegenAsymp.unit_class]
    exact AsymptoticSpectrum.eval_natCast _ _ _
  simpa [hu] using! H

end OM.PolMul.Superadditivity
