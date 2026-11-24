/- Adapted from PolMul/TriplingDegeneration.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Amanov, van den Berg and Zuiddam (2026),
   “Multiplying matrices via polynomials: exposition and barriers”.
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMulStatements.TP_1
import Mathlib.Tactic

/-!
# The tripling degeneration

This is the explicit monomial degeneration in Section 3.4.
The second-leg block sizes are `b, a+b-1, b`, and the third-leg block
sizes are `a+b-1, b, a+b-1`.  The coordinates in both middle blocks are
reversed.
-/

namespace OM.PolMul.TriplingDegeneration

open OM.PolMulDef
open scoped BigOperators

universe u

private def summandFmt (a b : ℕ+) : Fin 3 → Fin 3 → ℕ+
  | 0 => fmt a b (a + b - 1)
  | 1 => fmt a (a + b - 1) b
  | 2 => fmt a b (a + b - 1)

private def rowSize (a b : ℕ+) : Fin 3 → ℕ
  | 0 => b
  | 1 => ((a + b - 1 : ℕ+) : ℕ)
  | 2 => b

private def colSize (a b : ℕ+) : Fin 3 → ℕ
  | 0 => ((a + b - 1 : ℕ+) : ℕ)
  | 1 => b
  | 2 => ((a + b - 1 : ℕ+) : ℕ)

private lemma summandFmt_row (a b : ℕ+) (i : Fin 3) :
    ((summandFmt a b i 1 : ℕ)) = rowSize a b i := by
  fin_cases i <;> rfl

private lemma summandFmt_col (a b : ℕ+) (i : Fin 3) :
    ((summandFmt a b i 2 : ℕ)) = colSize a b i := by
  fin_cases i <;> rfl

private lemma summandFmt_first (a b : ℕ+) (i : Fin 3) :
    summandFmt a b i 0 = a := by
  fin_cases i <;> rfl

private lemma rowTotal_eq (a b : ℕ+) :
    (∑ i : Fin 3, rowSize a b i) = ((3 * b + a - 1 : ℕ+) : ℕ) := by
  rw [Fin.sum_univ_three]
  simp only [rowSize]
  pnat_to_nat
  omega

private lemma colTotal_eq (a b : ℕ+) :
    (∑ i : Fin 3, colSize a b i) =
      ((a + (3 * b + a - 1) - 1 : ℕ+) : ℕ) := by
  rw [Fin.sum_univ_three]
  simp only [colSize]
  pnat_to_nat
  omega

/-- Reverse precisely the middle row block. -/
private def sourceRowNat (a b : ℕ+) (x : ℕ) : ℕ :=
  if x < (b : ℕ) then x
  else if x < (b : ℕ) + rowSize a b 1 then
    (b : ℕ) + ((b : ℕ) + rowSize a b 1 - 1 - x)
  else x

/-- Reverse precisely the middle column block. -/
private def sourceColNat (a b : ℕ+) (x : ℕ) : ℕ :=
  if x < colSize a b 0 then x
  else if x < colSize a b 0 + (b : ℕ) then
    colSize a b 0 + (colSize a b 0 + (b : ℕ) - 1 - x)
  else x

private def rowWeightNat (a b : ℕ+) (x : ℕ) : ℕ :=
  if (b : ℕ) ≤ x ∧ x < (b : ℕ) + rowSize a b 1 then 1 else 0

private def colWeightNat (a b : ℕ+) (x : ℕ) : ℕ :=
  if colSize a b 0 ≤ x ∧ x < colSize a b 0 + (b : ℕ) then 0 else 1

private def targetFmt (a b : ℕ+) : Fin 3 → ℕ+ :=
  fmt a
    ⟨∑ i : Fin 3, (summandFmt a b i 1 : ℕ),
      Finset.sum_pos (fun i _ => (summandFmt a b i 1).pos) Finset.univ_nonempty⟩
    ⟨∑ i : Fin 3, (summandFmt a b i 2 : ℕ),
      Finset.sum_pos (fun i _ => (summandFmt a b i 2).pos) Finset.univ_nonempty⟩

private def sourceFmt (a b : ℕ+) : Fin 3 → ℕ+ :=
  fmt a (3 * b + a - 1) (a + (3 * b + a - 1) - 1)

private def summandTensor {F : Type u} [Field F] (a b : ℕ+) :
    ∀ i : Fin 3, T3 F (summandFmt a b i)
  | 0 => polmul a b
  | 1 => swap23' (polmul a b)
  | 2 => polmul a b

private noncomputable def targetTensor {F : Type u} [Field F] (a b : ℕ+) :
    T3 F (targetFmt a b) :=
  pdsumFamily (summandFmt a b) a
    (fun | 0 => rfl | 1 => rfl | 2 => rfl)
    (summandTensor a b)

/- Packaging the dependent block coordinates as arguments of one function lets
us transport them without exposing the casts inside `pdsumFamily`. -/
private noncomputable def targetEval {F : Type u} [Field F] (a b : ℕ+) (x : Fin a)
    (iv : (i : Fin 3) × Fin (summandFmt a b i 1))
    (iw : (i : Fin 3) × Fin (summandFmt a b i 2)) : F :=
  if hi : iv.1 = iw.1 then
    summandTensor a b iv.1 (fun
      | 0 => Fin.cast
          (congrArg (fun z : ℕ+ => (z : ℕ)) (summandFmt_first a b iv.1).symm) x
      | 1 => iv.2
      | 2 => Fin.cast (by rw [hi]) iw.2)
  else 0

private lemma targetTensor_eq_targetEval {F : Type u} [Field F] (a b : ℕ+)
    (idx : ∀ i : Fin 3, Fin (targetFmt a b i)) :
    targetTensor (F := F) a b idx =
      targetEval a b (idx 0) (finSigmaFinEquiv.symm (idx 1))
        (finSigmaFinEquiv.symm (idx 2)) := by
  rfl

private def sourceTensor {F : Type u} [Field F] (a b : ℕ+) :
    T3 F (sourceFmt a b) := polmul a (3 * b + a - 1)

private lemma sourceRowNat_lt (a b : ℕ+) {x : ℕ}
    (hx : x < ∑ i : Fin 3, rowSize a b i) :
    sourceRowNat a b x < ((3 * b + a - 1 : ℕ+) : ℕ) := by
  rw [← rowTotal_eq a b]
  rw [Fin.sum_univ_three] at hx ⊢
  simp only [rowSize] at hx ⊢
  unfold sourceRowNat
  simp only [rowSize]
  split_ifs <;> omega

private lemma sourceColNat_lt (a b : ℕ+) {x : ℕ}
    (hx : x < ∑ i : Fin 3, colSize a b i) :
    sourceColNat a b x <
      ((a + (3 * b + a - 1) - 1 : ℕ+) : ℕ) := by
  rw [← colTotal_eq a b]
  rw [Fin.sum_univ_three] at hx ⊢
  simp only [colSize] at hx ⊢
  unfold sourceColNat
  simp only [colSize]
  split_ifs <;> omega

private def rowMap (a b : ℕ+) (x : Fin (targetFmt a b 1)) :
    Fin (sourceFmt a b 1) :=
  ⟨sourceRowNat a b x, by
    apply sourceRowNat_lt
    have hx := x.isLt
    simpa only [targetFmt, fmt, summandFmt_row] using! hx⟩

private def colMap (a b : ℕ+) (x : Fin (targetFmt a b 2)) :
    Fin (sourceFmt a b 2) :=
  ⟨sourceColNat a b x, by
    apply sourceColNat_lt
    have hx := x.isLt
    simpa only [targetFmt, fmt, summandFmt_col] using! hx⟩

private def coordMap (a b : ℕ+) :
    ∀ i : Fin 3, Fin (targetFmt a b i) → Fin (sourceFmt a b i)
  | 0, x => x
  | 1, x => rowMap a b x
  | 2, x => colMap a b x

private def coordWeight (a b : ℕ+) :
    ∀ i : Fin 3, Fin (targetFmt a b i) → ℕ
  | 0, _ => 0
  | 1, x => rowWeightNat a b x
  | 2, x => colWeightNat a b x

private lemma sum_delta {R : Type*} [CommSemiring R] {d : Fin 3 → ℕ+}
    (pick : ∀ i : Fin 3, Fin (d i)) (c : Fin 3 → R) (f : (∀ i, Fin (d i)) → R) :
    (∑ x : (∀ i : Fin 3, Fin (d i)),
      (∏ i : Fin 3, if x i = pick i then c i else 0) * f x) =
      (∏ i : Fin 3, c i) * f pick := by
  classical
  rw [Fintype.sum_eq_single pick]
  · simp
  · intro x hx
    have hcoord : ∃ i, x i ≠ pick i := by
      by_contra h
      push_neg at h
      exact hx (funext h)
    obtain ⟨i, hi⟩ := hcoord
    have hp : (∏ j : Fin 3, if x j = pick j then c j else 0) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hi]
    simp [hp]

private def totalWeight (a b : ℕ+)
    (idx : ∀ i : Fin 3, Fin (targetFmt a b i)) : ℕ :=
  ∑ i : Fin 3, coordWeight a b i (idx i)

private lemma totalWeight_eq (a b : ℕ+)
    (idx : ∀ i : Fin 3, Fin (targetFmt a b i)) :
    totalWeight a b idx =
      rowWeightNat a b (idx 1).val + colWeightNat a b (idx 2).val := by
  simp [totalWeight, Fin.sum_univ_three, coordWeight]

private def selectedSource {F : Type u} [Field F] (a b : ℕ+)
    (idx : ∀ i : Fin 3, Fin (targetFmt a b i)) : F :=
  sourceTensor a b (fun i => coordMap a b i (idx i))

private def errorTensor {F : Type u} [Field F] (a b : ℕ+) :
    T3 F (targetFmt a b) :=
  fun idx => if totalWeight a b idx = 2 then selectedSource (F := F) a b idx else 0

private lemma totalWeight_le_two (a b : ℕ+)
    (idx : ∀ i : Fin 3, Fin (targetFmt a b i)) :
    totalWeight a b idx ≤ 2 := by
  rw [show totalWeight a b idx =
      rowWeightNat a b (idx 1).val + colWeightNat a b (idx 2).val by
    simp [totalWeight, Fin.sum_univ_three, coordWeight]]
  unfold rowWeightNat colWeightNat
  split_ifs <;> omega

private def blockIndex (a b : ℕ+) (x : Fin a)
    (ri : Fin 3) (r : Fin (summandFmt a b ri 1))
    (ci : Fin 3) (c : Fin (summandFmt a b ci 2)) :
    ∀ i : Fin 3, Fin (targetFmt a b i)
  | 0 => x
  | 1 => finSigmaFinEquiv
      (n := fun i => (summandFmt a b i 1 : ℕ)) ⟨ri, r⟩
  | 2 => finSigmaFinEquiv
      (n := fun i => (summandFmt a b i 2 : ℕ)) ⟨ci, c⟩

@[simp] private lemma rowFlat_zero (a b : ℕ+) (r : Fin (summandFmt a b 0 1)) :
    (finSigmaFinEquiv
      (n := fun i => (summandFmt a b i 1 : ℕ)) ⟨(0 : Fin 3), r⟩).val = r.val := by
  rw [finSigmaFinEquiv_apply]
  simp

@[simp] private lemma rowFlat_one (a b : ℕ+) (r : Fin (summandFmt a b 1 1)) :
    (finSigmaFinEquiv
      (n := fun i => (summandFmt a b i 1 : ℕ)) ⟨(1 : Fin 3), r⟩).val =
      (b : ℕ) + r.val := by
  rw [finSigmaFinEquiv_apply]
  simp [Fin.sum_univ_succ, summandFmt, fmt]

@[simp] private lemma rowFlat_two (a b : ℕ+) (r : Fin (summandFmt a b 2 1)) :
    (finSigmaFinEquiv
      (n := fun i => (summandFmt a b i 1 : ℕ)) ⟨(2 : Fin 3), r⟩).val =
      (b : ℕ) + ((a + b - 1 : ℕ+) : ℕ) + r.val := by
  rw [finSigmaFinEquiv_apply]
  simp [Fin.sum_univ_succ, summandFmt, fmt]

@[simp] private lemma colFlat_zero (a b : ℕ+) (c : Fin (summandFmt a b 0 2)) :
    (finSigmaFinEquiv
      (n := fun i => (summandFmt a b i 2 : ℕ)) ⟨(0 : Fin 3), c⟩).val = c.val := by
  rw [finSigmaFinEquiv_apply]
  simp

@[simp] private lemma colFlat_one (a b : ℕ+) (c : Fin (summandFmt a b 1 2)) :
    (finSigmaFinEquiv
      (n := fun i => (summandFmt a b i 2 : ℕ)) ⟨(1 : Fin 3), c⟩).val =
      ((a + b - 1 : ℕ+) : ℕ) + c.val := by
  rw [finSigmaFinEquiv_apply]
  simp [Fin.sum_univ_succ, summandFmt, fmt]

@[simp] private lemma colFlat_two (a b : ℕ+) (c : Fin (summandFmt a b 2 2)) :
    (finSigmaFinEquiv
      (n := fun i => (summandFmt a b i 2 : ℕ)) ⟨(2 : Fin 3), c⟩).val =
      ((a + b - 1 : ℕ+) : ℕ) + (b : ℕ) + c.val := by
  rw [finSigmaFinEquiv_apply]
  simp [Fin.sum_univ_succ, summandFmt, fmt]

@[simp] private lemma sourceRow_zero (a b : ℕ+)
    (r : Fin (summandFmt a b 0 1)) :
    sourceRowNat a b r.val = r.val := by
  have hr := r.isLt
  simp only [summandFmt, fmt] at hr
  unfold sourceRowNat
  split_ifs <;> omega

@[simp] private lemma sourceRow_one (a b : ℕ+)
    (r : Fin (summandFmt a b 1 1)) :
    sourceRowNat a b ((b : ℕ) + r.val) =
      (b : ℕ) + (((a + b - 1 : ℕ+) : ℕ) - 1 - r.val) := by
  have hr := r.isLt
  simp only [summandFmt, fmt] at hr
  unfold sourceRowNat
  simp only [rowSize]
  pnat_to_nat
  split_ifs <;> omega

private lemma middle_index_iff (a b : ℕ+) (x : Fin a)
    (r : Fin (summandFmt a b 1 1)) (c : Fin (summandFmt a b 1 2)) :
    ((a + b - 1 : ℕ+) : ℕ) + ((b : ℕ) - 1 - c.val) =
        x.val + ((b : ℕ) + (((a + b - 1 : ℕ+) : ℕ) - 1 - r.val)) ↔
      r.val = x.val + c.val := by
  have hr := r.isLt
  have hc := c.isLt
  simp only [summandFmt, fmt] at hr hc
  pnat_to_nat
  omega

private lemma outer_two_index_iff (a b : ℕ+) (x : Fin a)
    (r : Fin (summandFmt a b 2 1)) (c : Fin (summandFmt a b 2 2)) :
    ((a + b - 1 : ℕ+) : ℕ) + (b : ℕ) + c.val =
        x.val + ((b : ℕ) + ((a + b - 1 : ℕ+) : ℕ) + r.val) ↔
      c.val = x.val + r.val := by
  omega

@[simp] private lemma sourceRow_two (a b : ℕ+)
    (r : Fin (summandFmt a b 2 1)) :
    sourceRowNat a b
        ((b : ℕ) + ((a + b - 1 : ℕ+) : ℕ) + r.val) =
      (b : ℕ) + ((a + b - 1 : ℕ+) : ℕ) + r.val := by
  have hr := r.isLt
  simp only [summandFmt, fmt] at hr
  unfold sourceRowNat
  simp only [rowSize]
  pnat_to_nat
  split_ifs <;> omega

@[simp] private lemma sourceCol_zero (a b : ℕ+)
    (c : Fin (summandFmt a b 0 2)) :
    sourceColNat a b c.val = c.val := by
  have hc := c.isLt
  simp only [summandFmt, fmt] at hc
  unfold sourceColNat
  simp only [colSize]
  pnat_to_nat
  split_ifs <;> omega

@[simp] private lemma sourceCol_one (a b : ℕ+)
    (c : Fin (summandFmt a b 1 2)) :
    sourceColNat a b (((a + b - 1 : ℕ+) : ℕ) + c.val) =
      ((a + b - 1 : ℕ+) : ℕ) + ((b : ℕ) - 1 - c.val) := by
  have hc := c.isLt
  simp only [summandFmt, fmt] at hc
  unfold sourceColNat
  simp only [colSize]
  pnat_to_nat
  split_ifs <;> omega

@[simp] private lemma sourceCol_two (a b : ℕ+)
    (c : Fin (summandFmt a b 2 2)) :
    sourceColNat a b
        (((a + b - 1 : ℕ+) : ℕ) + (b : ℕ) + c.val) =
      ((a + b - 1 : ℕ+) : ℕ) + (b : ℕ) + c.val := by
  have hc := c.isLt
  simp only [summandFmt, fmt] at hc
  unfold sourceColNat
  simp only [colSize]
  pnat_to_nat
  split_ifs <;> omega

private lemma target_offDiag {F : Type u} [Field F] (a b : ℕ+) (x : Fin a)
    (ri : Fin 3) (r : Fin (summandFmt a b ri 1))
    (ci : Fin 3) (c : Fin (summandFmt a b ci 2)) (h : ri ≠ ci) :
    targetTensor (F := F) a b (blockIndex a b x ri r ci c) = 0 := by
  classical
  simp [targetTensor, pdsumFamily, blockIndex, h]

-- These three cases are the paper's two outer copies and its reversed middle copy.
set_option maxHeartbeats 400000 in
private lemma target_diagonal_eq_selected {F : Type u} [Field F]
    (a b : ℕ+) (x : Fin a) (i : Fin 3)
    (r : Fin (summandFmt a b i 1)) (c : Fin (summandFmt a b i 2)) :
    targetTensor (F := F) a b (blockIndex a b x i r i c) =
      selectedSource (F := F) a b (blockIndex a b x i r i c) := by
  classical
  have hr : r.val < rowSize a b i := by
    rw [← summandFmt_row]
    exact r.isLt
  have hc : c.val < colSize a b i := by
    rw [← summandFmt_col]
    exact c.isLt
  rw [targetTensor_eq_targetEval]
  have hrow : finSigmaFinEquiv.symm ((blockIndex a b x i r i c) 1) = ⟨i, r⟩ := by
    simp [blockIndex]
  have hcol : finSigmaFinEquiv.symm ((blockIndex a b x i r i c) 2) = ⟨i, c⟩ := by
    simp [blockIndex]
  change targetEval (F := F) a b x
      (finSigmaFinEquiv.symm ((blockIndex a b x i r i c) 1))
      (finSigmaFinEquiv.symm ((blockIndex a b x i r i c) 2)) = _
  rw [show targetEval (F := F) a b x
      (finSigmaFinEquiv.symm ((blockIndex a b x i r i c) 1))
      (finSigmaFinEquiv.symm ((blockIndex a b x i r i c) 2)) =
        targetEval a b x ⟨i, r⟩ ⟨i, c⟩ by
    exact congrArg₂ (targetEval (F := F) a b x) hrow hcol]
  fin_cases i <;>
    simp only [rowSize, colSize] at hr hc <;>
    simp [targetEval, summandTensor, blockIndex, summandFmt, fmt, swap23', polmul,
      selectedSource, sourceTensor, sourceFmt,
      coordMap, rowMap, colMap, Fin.val_mk,
      rowFlat_zero, rowFlat_one, rowFlat_two, colFlat_zero, colFlat_one,
      colFlat_two, sourceRow_zero, sourceRow_one, sourceRow_two,
      sourceCol_zero, sourceCol_one, sourceCol_two,
      middle_index_iff, outer_two_index_iff,
      rowSize, colSize, Fin.val_cast] <;>
    pnat_to_nat <;> split_ifs <;> omega

-- Outside the middle row every off-diagonal source block is zero.
set_option maxHeartbeats 400000 in
private lemma selectedSource_offDiag_zero {F : Type u} [Field F]
    (a b : ℕ+) (x : Fin a) (ri : Fin 3)
    (r : Fin (summandFmt a b ri 1)) (ci : Fin 3)
    (c : Fin (summandFmt a b ci 2)) (hm : ri ≠ 1) (hd : ri ≠ ci) :
    selectedSource (F := F) a b (blockIndex a b x ri r ci c) = 0 := by
  classical
  have hr : r.val < rowSize a b ri := by
    rw [← summandFmt_row]
    exact r.isLt
  have hc : c.val < colSize a b ci := by
    rw [← summandFmt_col]
    exact c.isLt
  fin_cases ri <;> fin_cases ci <;>
    try { exact (hm rfl).elim } <;>
    try { exact (hd rfl).elim } <;>
    simp only [rowSize, colSize] at hr hc <;>
    simp [selectedSource, sourceTensor, sourceFmt, blockIndex, summandFmt,
      fmt, polmul, coordMap, rowMap, colMap, Fin.val_mk, sourceRowNat,
      sourceColNat, rowFlat_zero, rowFlat_one, rowFlat_two, colFlat_zero,
      colFlat_one, colFlat_two, rowSize, colSize] <;>
    pnat_to_nat <;> omega

private lemma diagonal_weight (a b : ℕ+) (x : Fin a) (i : Fin 3)
    (r : Fin (summandFmt a b i 1)) (c : Fin (summandFmt a b i 2)) :
    totalWeight a b (blockIndex a b x i r i c) = 1 := by
  have hr : r.val < rowSize a b i := by
    rw [← summandFmt_row]
    exact r.isLt
  have hc : c.val < colSize a b i := by
    rw [← summandFmt_col]
    exact c.isLt
  rw [totalWeight_eq]
  fin_cases i <;>
    simp only [rowSize, colSize] at hr hc <;>
    simp [blockIndex, rowWeightNat, colWeightNat, rowFlat_zero, rowFlat_one,
      rowFlat_two, colFlat_zero, colFlat_one, colFlat_two, rowSize, colSize,
      summandFmt, fmt, Fin.val_mk] <;> pnat_to_nat <;> split_ifs <;> omega

private lemma middle_offDiag_weight (a b : ℕ+) (x : Fin a)
    (r : Fin (summandFmt a b 1 1)) (ci : Fin 3)
    (c : Fin (summandFmt a b ci 2)) (hd : (1 : Fin 3) ≠ ci) :
    totalWeight a b (blockIndex a b x 1 r ci c) = 2 := by
  have hr : r.val < rowSize a b 1 := by
    rw [← summandFmt_row]
    exact r.isLt
  have hc : c.val < colSize a b ci := by
    rw [← summandFmt_col]
    exact c.isLt
  rw [totalWeight_eq]
  fin_cases ci <;>
    try { exact (hd rfl).elim } <;>
    simp only [rowSize, colSize] at hr hc <;>
    simp [blockIndex, rowWeightNat, colWeightNat,
      rowFlat_zero, rowFlat_one, rowFlat_two, colFlat_zero, colFlat_one,
      colFlat_two, rowSize, colSize, summandFmt, fmt, Fin.val_mk] <;>
    pnat_to_nat <;> split_ifs <;> omega

/- The only substantial index computation: degree one is exactly the three
diagonal blocks, while degree zero has no source support. -/
private lemma block_selection {F : Type u} [Field F] (a b : ℕ+)
    (idx : ∀ i : Fin 3, Fin (targetFmt a b i)) :
    (targetTensor (F := F) a b idx =
        if totalWeight a b idx = 1 then selectedSource (F := F) a b idx else 0) ∧
      (totalWeight a b idx = 0 → selectedSource (F := F) a b idx = 0) := by
  classical
  generalize hv : finSigmaFinEquiv.symm (idx 1) = iv
  generalize hw : finSigmaFinEquiv.symm (idx 2) = iw
  rcases iv with ⟨ri, r⟩
  rcases iw with ⟨ci, c⟩
  have hidx : idx = blockIndex a b (idx 0) ri r ci c := by
    funext j
    fin_cases j
    · rfl
    · exact (calc
        idx 1 = finSigmaFinEquiv (finSigmaFinEquiv.symm (idx 1)) :=
          (finSigmaFinEquiv.apply_symm_apply (idx 1)).symm
        _ = finSigmaFinEquiv
            (n := fun i => (summandFmt a b i 1 : ℕ)) ⟨ri, r⟩ :=
          congrArg finSigmaFinEquiv hv)
    · exact (calc
        idx 2 = finSigmaFinEquiv (finSigmaFinEquiv.symm (idx 2)) :=
          (finSigmaFinEquiv.apply_symm_apply (idx 2)).symm
        _ = finSigmaFinEquiv
            (n := fun i => (summandFmt a b i 2 : ℕ)) ⟨ci, c⟩ :=
          congrArg finSigmaFinEquiv hw)
  rw [hidx]
  by_cases hd : ri = ci
  · subst ci
    rw [diagonal_weight, target_diagonal_eq_selected]
    simp
  · rw [target_offDiag _ _ _ _ _ _ _ hd]
    by_cases hm : ri = 1
    · subst ri
      rw [middle_offDiag_weight (a := a) (b := b) (x := idx 0)
        (r := r) (ci := ci) (c := c) hd]
      simp
    · rw [selectedSource_offDiag_zero _ _ _ _ _ _ _ hm hd]
      simp

/-- The monomial matrices: one nonzero entry in each target row, composed with
the reversal permutations on the two middle blocks. -/
private noncomputable def degenMatrix {F : Type u} [Field F] (a b : ℕ+) :
    ∀ i : Fin 3,
      Matrix (Fin (targetFmt a b i)) (Fin (sourceFmt a b i)) (Polynomial F) :=
  fun i x y =>
    if y = coordMap a b i x then Polynomial.X ^ coordWeight a b i x else 0

private lemma monomialProduct {F : Type u} [Field F] (a b : ℕ+)
    (idx : ∀ i : Fin 3, Fin (targetFmt a b i)) :
    (∏ i : Fin 3, (Polynomial.X : Polynomial F) ^ coordWeight a b i (idx i)) =
      Polynomial.X ^ totalWeight a b idx := by
  rw [Fin.prod_univ_three, totalWeight_eq]
  simp [coordWeight, pow_add]

private lemma coefficient_identity {F : Type u} [Field F] (a b : ℕ+)
    (idx : ∀ i : Fin 3, Fin (targetFmt a b i)) :
    Polynomial.X ^ totalWeight a b idx *
        Polynomial.C (selectedSource (F := F) a b idx) =
      Polynomial.X * Polynomial.C (targetTensor (F := F) a b idx) +
        Polynomial.X ^ 2 * Polynomial.C (errorTensor (F := F) a b idx) := by
  obtain ⟨ht, hz⟩ := block_selection (F := F) a b idx
  have hw := totalWeight_le_two a b idx
  interval_cases hweight : totalWeight a b idx
  · have hs : selectedSource (F := F) a b idx = 0 := hz rfl
    have ht0 : targetTensor (F := F) a b idx = 0 := by
      simpa [hweight] using! ht
    simp [hweight, hs, ht0, errorTensor]
  · have ht1 : targetTensor (F := F) a b idx =
        selectedSource (F := F) a b idx := by
      simpa [hweight] using! ht
    simp [hweight, ht1, errorTensor]
  · have ht2 : targetTensor (F := F) a b idx = 0 := by
      simpa [hweight] using! ht
    simp [hweight, ht2, errorTensor]

-- The coefficient computation expands the finite tensor action once.
set_option maxHeartbeats 400000 in
private theorem triplingDegen {F : Type u} [Field F] (a b : ℕ+) :
    Degen23 (targetTensor (F := F) a b) (sourceTensor (F := F) a b) rfl := by
  classical
  refine ⟨1, 1, degenMatrix a b, fun _ => errorTensor a b, ?_, ?_⟩
  · intro x y
    simp [degenMatrix, coordMap, coordWeight, eq_comm]
  · intro idx
    calc
      (∑ sidx : (∀ i : Fin 3, Fin (sourceFmt a b i)),
          (∏ i : Fin 3, degenMatrix a b i (idx i) (sidx i)) *
            Polynomial.C (sourceTensor a b sidx)) =
          (∏ i : Fin 3,
              (Polynomial.X : Polynomial F) ^ coordWeight a b i (idx i)) *
            Polynomial.C (sourceTensor a b
              (fun i => coordMap a b i (idx i))) := by
        simpa only [degenMatrix] using!
          (sum_delta (R := Polynomial F)
            (fun i => coordMap a b i (idx i))
            (fun i => Polynomial.X ^ coordWeight a b i (idx i))
            (fun sidx => Polynomial.C (sourceTensor a b sidx)))
      _ = Polynomial.X ^ totalWeight a b idx *
            Polynomial.C (selectedSource (F := F) a b idx) := by
        rw [monomialProduct]
        rfl
      _ = Polynomial.X * Polynomial.C (targetTensor (F := F) a b idx) +
            Polynomial.X ^ 2 * Polynomial.C (errorTensor (F := F) a b idx) :=
        coefficient_identity a b idx
      _ = Polynomial.X ^ 1 * Polynomial.C (targetTensor (F := F) a b idx) +
            ∑ j : Fin 1,
              Polynomial.X ^ (1 + j.val + 1) *
                Polynomial.C ((fun _ => errorTensor (F := F) a b) j idx) := by
        simp

-- The public statement is definitionally the block tensor used above.
set_option maxHeartbeats 400000 in
theorem proof_TP_1 : OM_S_TP_1 := by
  unfold OM_S_TP_1
  intro F _ a b
  exact triplingDegen (F := F) a b

end OM.PolMul.TriplingDegeneration
