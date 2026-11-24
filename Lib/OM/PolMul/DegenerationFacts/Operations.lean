/- Adapted from PolMul/DegenerationFacts/Operations.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMul.DegenerationFacts.Core

/-!
# Tensor-operation calculations for polynomial arcs

The coordinate lemmas here are semiring-valued versions of the restriction
calculations in the dependency's `TensorSemiring` module.
-/

namespace OM.PolMul.DegenerationFacts

open Semicontinuity
open scoped BigOperators

universe v

variable {R : Type v} [CommSemiring R]

/-- Block-diagonal sum of two arrays over an arbitrary commutative semiring. -/
noncomputable def rawDsum {d₁ d₂ : Fin 3 → ℕ+}
    (S : (∀ i : Fin 3, Fin (d₁ i)) → R)
    (T : (∀ i : Fin 3, Fin (d₂ i)) → R) :
    (∀ i : Fin 3, Fin ((d₁ i + d₂ i : ℕ+) : ℕ)) → R := by
  classical
  intro idx
  by_cases hS : ∀ i, (idx i).val < (d₁ i : ℕ)
  · exact S (fun i ↦ ⟨(idx i).val, hS i⟩)
  · by_cases hT : ∀ i, (d₁ i : ℕ) ≤ (idx i).val
    · exact T (fun i ↦ ⟨(idx i).val - (d₁ i : ℕ), by
        have hi := (idx i).isLt
        have hc := PNat.add_coe (d₁ i) (d₂ i)
        have hp := (d₂ i).pos
        omega⟩)
    · exact 0

lemma rawDsum_apply {d₁ d₂ : Fin 3 → ℕ+}
    (S : (∀ i : Fin 3, Fin (d₁ i)) → R)
    (T : (∀ i : Fin 3, Fin (d₂ i)) → R)
    (idx : ∀ i : Fin 3, Fin ((d₁ i + d₂ i : ℕ+) : ℕ)) :
    rawDsum S T idx =
      if hS : ∀ i, (idx i).val < (d₁ i : ℕ) then
        S (fun i ↦ ⟨(idx i).val, hS i⟩)
      else if _hT : ∀ i, (d₁ i : ℕ) ≤ (idx i).val then
        T (fun i ↦ ⟨(idx i).val - (d₁ i : ℕ), by
          have hi := (idx i).isLt
          have hc := PNat.add_coe (d₁ i) (d₂ i)
          have hp := (d₂ i).pos
          omega⟩)
      else 0 := by
  classical
  unfold rawDsum
  by_cases hS : ∀ i, (idx i).val < (d₁ i : ℕ)
  · simp only [dif_pos hS]
  · by_cases hT : ∀ i, (d₁ i : ℕ) ≤ (idx i).val
    · simp only [dif_neg hS, dif_pos hT]
    · simp only [dif_neg hS, dif_neg hT]

/-- A block-diagonal family of leg matrices over an arbitrary semiring. -/
noncomputable def blockDiag {dS₁ dT₁ dS₂ dT₂ : Fin 3 → ℕ+}
    (A : ∀ i : Fin 3, Matrix (Fin (dS₁ i)) (Fin (dT₁ i)) R)
    (B : ∀ i : Fin 3, Matrix (Fin (dS₂ i)) (Fin (dT₂ i)) R)
    (i : Fin 3) : Matrix (Fin ((dS₁ i + dS₂ i : ℕ+) : ℕ))
      (Fin ((dT₁ i + dT₂ i : ℕ+) : ℕ)) R :=
  fun a b ↦
    if ha : a.val < (dS₁ i : ℕ) then
      if hb : b.val < (dT₁ i : ℕ) then A i ⟨a.val, ha⟩ ⟨b.val, hb⟩ else 0
    else if hb : (dT₁ i : ℕ) ≤ b.val then
      B i ⟨a.val - (dS₁ i : ℕ), by
        have ha' := a.isLt
        have hc := PNat.add_coe (dS₁ i) (dS₂ i)
        omega⟩
        ⟨b.val - (dT₁ i : ℕ), by
          have hb' := b.isLt
          have hc := PNat.add_coe (dT₁ i) (dT₂ i)
          omega⟩
    else 0

lemma blockDiag_left {dS₁ dT₁ dS₂ dT₂ : Fin 3 → ℕ+}
    (A : ∀ i : Fin 3, Matrix (Fin (dS₁ i)) (Fin (dT₁ i)) R)
    (B : ∀ i : Fin 3, Matrix (Fin (dS₂ i)) (Fin (dT₂ i)) R) (i : Fin 3)
    {a : Fin ((dS₁ i + dS₂ i : ℕ+) : ℕ)}
    {b : Fin ((dT₁ i + dT₂ i : ℕ+) : ℕ)}
    (ha : a.val < (dS₁ i : ℕ)) (hb : b.val < (dT₁ i : ℕ)) :
    blockDiag A B i a b = A i ⟨a.val, ha⟩ ⟨b.val, hb⟩ := by
  simp [blockDiag, ha, hb]

lemma blockDiag_left_right_zero {dS₁ dT₁ dS₂ dT₂ : Fin 3 → ℕ+}
    (A : ∀ i : Fin 3, Matrix (Fin (dS₁ i)) (Fin (dT₁ i)) R)
    (B : ∀ i : Fin 3, Matrix (Fin (dS₂ i)) (Fin (dT₂ i)) R) (i : Fin 3)
    {a : Fin ((dS₁ i + dS₂ i : ℕ+) : ℕ)}
    {b : Fin ((dT₁ i + dT₂ i : ℕ+) : ℕ)}
    (ha : a.val < (dS₁ i : ℕ)) (hb : (dT₁ i : ℕ) ≤ b.val) :
    blockDiag A B i a b = 0 := by simp [blockDiag, ha, show ¬ b.val < (dT₁ i : ℕ) by omega]

lemma blockDiag_right {dS₁ dT₁ dS₂ dT₂ : Fin 3 → ℕ+}
    (A : ∀ i : Fin 3, Matrix (Fin (dS₁ i)) (Fin (dT₁ i)) R)
    (B : ∀ i : Fin 3, Matrix (Fin (dS₂ i)) (Fin (dT₂ i)) R) (i : Fin 3)
    {a : Fin ((dS₁ i + dS₂ i : ℕ+) : ℕ)}
    {b : Fin ((dT₁ i + dT₂ i : ℕ+) : ℕ)}
    (ha : (dS₁ i : ℕ) ≤ a.val) (hb : (dT₁ i : ℕ) ≤ b.val) :
    blockDiag A B i a b =
      B i ⟨a.val - (dS₁ i : ℕ), by
        have hc := PNat.add_coe (dS₁ i) (dS₂ i); omega⟩
        ⟨b.val - (dT₁ i : ℕ), by
          have hc := PNat.add_coe (dT₁ i) (dT₂ i); omega⟩ := by
  simp [blockDiag, show ¬ a.val < (dS₁ i : ℕ) by omega, hb]

lemma blockDiag_right_left_zero {dS₁ dT₁ dS₂ dT₂ : Fin 3 → ℕ+}
    (A : ∀ i : Fin 3, Matrix (Fin (dS₁ i)) (Fin (dT₁ i)) R)
    (B : ∀ i : Fin 3, Matrix (Fin (dS₂ i)) (Fin (dT₂ i)) R) (i : Fin 3)
    {a : Fin ((dS₁ i + dS₂ i : ℕ+) : ℕ)}
    {b : Fin ((dT₁ i + dT₂ i : ℕ+) : ℕ)}
    (ha : (dS₁ i : ℕ) ≤ a.val) (hb : b.val < (dT₁ i : ℕ)) :
    blockDiag A B i a b = 0 := by
  simp [blockDiag, show ¬ a.val < (dS₁ i : ℕ) by omega,
    show ¬ (dT₁ i : ℕ) ≤ b.val by omega]

/-- Block-diagonal leg maps act independently on the two direct summands. -/
lemma action_blockDiag {dS₁ dT₁ dS₂ dT₂ : Fin 3 → ℕ+}
    (A : ∀ i : Fin 3, Matrix (Fin (dS₁ i)) (Fin (dT₁ i)) R)
    (B : ∀ i : Fin 3, Matrix (Fin (dS₂ i)) (Fin (dT₂ i)) R)
    (S : (∀ i : Fin 3, Fin (dT₁ i)) → R)
    (T : (∀ i : Fin 3, Fin (dT₂ i)) → R)
    (jdx : ∀ i : Fin 3, Fin ((dS₁ i + dS₂ i : ℕ+) : ℕ)) :
    rawDsum (fun x ↦ action A S x) (fun x ↦ action B T x) jdx =
      action (blockDiag A B) (rawDsum S T) jdx := by
  classical
  rw [rawDsum_apply]
  by_cases hSL : ∀ i, (jdx i).val < (dS₁ i : ℕ)
  · simp only [dif_pos hSL]
    unfold action
    rw [← Finset.sum_subset
      (Finset.subset_univ ((Finset.univ : Finset (∀ i, Fin (dT₁ i))).image
        (Semicontinuity.dsumEmbLeft (d₂ := dT₂))))]
    · rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro w _
        congr 1
        · apply Finset.prod_congr rfl
          intro i _
          rw [blockDiag_left A B i (hSL i) (w i).isLt]
          rfl
        · rw [rawDsum_apply]
          simp only [Semicontinuity.dsumEmbLeft]
          rw [dif_pos (fun i ↦ (w i).isLt)]
      · intro x _ y _ hxy
        funext i
        apply Fin.ext
        exact congrArg (fun f ↦ (f i).val) hxy
    · intro idx _ hidx
      have hnot : ¬ ∀ i, (idx i).val < (dT₁ i : ℕ) := by
        intro hall
        apply hidx
        exact Finset.mem_image.2 ⟨fun i ↦ ⟨(idx i).val, hall i⟩, Finset.mem_univ _, by
          funext i; rfl⟩
      obtain ⟨i, hi⟩ := not_forall.1 hnot
      rw [Finset.prod_eq_zero (Finset.mem_univ i)
        (blockDiag_left_right_zero A B i (hSL i) (by omega)), zero_mul]
  · by_cases hSR : ∀ i, (dS₁ i : ℕ) ≤ (jdx i).val
    · simp only [dif_neg hSL, dif_pos hSR]
      unfold action
      rw [← Finset.sum_subset
        (Finset.subset_univ ((Finset.univ : Finset (∀ i, Fin (dT₂ i))).image
          (Semicontinuity.dsumEmbRight (d₁ := dT₁))))]
      · rw [Finset.sum_image]
        · apply Finset.sum_congr rfl
          intro w _
          congr 1
          · apply Finset.prod_congr rfl
            intro i _
            rw [blockDiag_right A B i (hSR i) (by
              simp [Semicontinuity.dsumEmbRight])]
            congr 2
            · apply Fin.ext
              simp [Semicontinuity.dsumEmbRight]
          · rw [rawDsum_apply]
            simp only [Semicontinuity.dsumEmbRight]
            rw [dif_neg (by
              intro hall
              have := hall 0
              have hp := (dT₁ 0).pos
              omega), dif_pos (fun i ↦ by omega)]
            congr 1
            funext i
            apply Fin.ext
            simp
        · intro x _ y _ hxy
          funext i
          have h := congrArg (fun f ↦ (f i).val) hxy
          apply Fin.ext
          simp [Semicontinuity.dsumEmbRight] at h
          omega
      · intro idx _ hidx
        have hnot : ¬ ∀ i, (dT₁ i : ℕ) ≤ (idx i).val := by
          intro hall
          apply hidx
          refine Finset.mem_image.2 ⟨fun i ↦ ⟨(idx i).val - (dT₁ i : ℕ), by
            have hi := (idx i).isLt
            have hc := PNat.add_coe (dT₁ i) (dT₂ i)
            have := hall i
            omega⟩, Finset.mem_univ _, ?_⟩
          funext i
          apply Fin.ext
          simp [Semicontinuity.dsumEmbRight]
          have := hall i
          omega
        obtain ⟨i, hi⟩ := not_forall.1 hnot
        rw [Finset.prod_eq_zero (Finset.mem_univ i)
          (blockDiag_right_left_zero A B i (hSR i) (by omega)), zero_mul]
    · simp only [dif_neg hSL, dif_neg hSR]
      unfold action
      symm
      apply Finset.sum_eq_zero
      intro idx _
      rw [rawDsum_apply]
      by_cases hidxL : ∀ i, (idx i).val < (dT₁ i : ℕ)
      · rw [dif_pos hidxL]
        obtain ⟨i, hi⟩ := not_forall.1 hSL
        rw [Finset.prod_eq_zero (Finset.mem_univ i)
          (blockDiag_right_left_zero A B i (by omega) (hidxL i)), zero_mul]
      · by_cases hidxR : ∀ i, (dT₁ i : ℕ) ≤ (idx i).val
        · rw [dif_neg hidxL, dif_pos hidxR]
          obtain ⟨i, hi⟩ := not_forall.1 hSR
          rw [Finset.prod_eq_zero (Finset.mem_univ i)
            (blockDiag_left_right_zero A B i (by omega) (hidxR i)), zero_mul]
        · rw [dif_neg hidxL, dif_neg hidxR, mul_zero]

/-- Multiply the map on leg zero by a scalar. -/
def scaleFirst {dT dS : Fin 3 → ℕ+} (c : R)
    (A : ∀ i : Fin 3, Matrix (Fin (dT i)) (Fin (dS i)) R) :
    ∀ i : Fin 3, Matrix (Fin (dT i)) (Fin (dS i)) R :=
  fun i x y ↦ if i = 0 then c * A i x y else A i x y

lemma action_scaleFirst {dT dS : Fin 3 → ℕ+} (c : R)
    (A : ∀ i : Fin 3, Matrix (Fin (dT i)) (Fin (dS i)) R)
    (S : (∀ i : Fin 3, Fin (dS i)) → R) (idx : ∀ i : Fin 3, Fin (dT i)) :
    action (scaleFirst c A) S idx = c * action A S idx := by
  unfold action
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have h10 : (1 : Fin 3) ≠ 0 := by decide +kernel
  have h20 : (2 : Fin 3) ≠ 0 := by decide +kernel
  simp only [Fin.prod_univ_three, scaleFirst, if_neg h10, if_neg h20, if_true]
  ring

/-- Kronecker product of two families of leg matrices. -/
def kronMatrix {dS₁ dT₁ dS₂ dT₂ : Fin 3 → ℕ+}
    (A : ∀ i : Fin 3, Matrix (Fin (dS₁ i)) (Fin (dT₁ i)) R)
    (B : ∀ i : Fin 3, Matrix (Fin (dS₂ i)) (Fin (dT₂ i)) R) :
    ∀ i : Fin 3, Matrix (Fin ((dS₁ i * dS₂ i : ℕ+) : ℕ))
      (Fin ((dT₁ i * dT₂ i : ℕ+) : ℕ)) R :=
  fun i a b ↦ A i (kronDecodeL a) (kronDecodeL b) *
    B i (kronDecodeR a) (kronDecodeR b)

/-- Kronecker leg matrices turn an action on a Kronecker tensor into the
product of the two separate actions.  This is the semiring-valued coordinate
calculation underlying `Restricts.kron_congr`. -/
lemma action_kronMatrix {dS₁ dT₁ dS₂ dT₂ : Fin 3 → ℕ+}
    (A : ∀ i : Fin 3, Matrix (Fin (dS₁ i)) (Fin (dT₁ i)) R)
    (B : ∀ i : Fin 3, Matrix (Fin (dS₂ i)) (Fin (dT₂ i)) R)
    (S : (∀ i : Fin 3, Fin (dT₁ i)) → R)
    (T : (∀ i : Fin 3, Fin (dT₂ i)) → R)
    (jdx : ∀ i : Fin 3, Fin ((dS₁ i * dS₂ i : ℕ+) : ℕ)) :
    action (kronMatrix A B)
        (fun idx ↦ S (kronLeftIndex idx) * T (kronRightIndex idx)) jdx =
      action A S (kronLeftIndex jdx) * action B T (kronRightIndex jdx) := by
  classical
  unfold action
  rw [Finset.sum_mul_sum]
  simp only [kronMatrix]
  set E : (∀ i, Fin ((dT₁ i * dT₂ i : ℕ+) : ℕ)) ≃
      (∀ i, Fin (dT₁ i)) × (∀ i, Fin (dT₂ i)) :=
    (Equiv.piCongrRight (fun _ ↦ kronDecodeEquiv)).trans
      (Equiv.arrowProdEquivProdArrow _ _ _) with hE
  rw [← Equiv.sum_comp E.symm
    (fun idx : ∀ i, Fin ((dT₁ i * dT₂ i : ℕ+) : ℕ) ↦
      (∏ i, (A i (kronDecodeL (jdx i)) (kronDecodeL (idx i)) *
        B i (kronDecodeR (jdx i)) (kronDecodeR (idx i)))) *
          (S (kronLeftIndex idx) * T (kronRightIndex idx)))]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro u _
  refine Finset.sum_congr rfl ?_
  intro v _
  have hdec : ∀ i, kronDecodeEquiv (E.symm (u, v) i) = (u i, v i) := by
    intro i
    have hsymm : E.symm (u, v) i = kronDecodeEquiv.symm (u i, v i) := by
      simp only [hE, Equiv.symm_trans_apply, Equiv.piCongrRight_symm_apply, Pi.map_apply,
        Equiv.arrowProdEquivProdArrow_symm_apply]
    rw [hsymm, Equiv.apply_symm_apply]
  have hL : ∀ i, kronDecodeL (d₁ := dT₁ i) (d₂ := dT₂ i)
      (E.symm (u, v) i) = u i := by
    intro i
    have h := hdec i
    rw [kronDecodeEquiv_apply] at h
    exact (Prod.ext_iff.1 h).1
  have hR : ∀ i, kronDecodeR (d₁ := dT₁ i) (d₂ := dT₂ i)
      (E.symm (u, v) i) = v i := by
    intro i
    have h := hdec i
    rw [kronDecodeEquiv_apply] at h
    exact (Prod.ext_iff.1 h).2
  have hKron : (∏ i, A i (kronDecodeL (jdx i)) (kronDecodeL (E.symm (u, v) i)) *
        B i (kronDecodeR (jdx i)) (kronDecodeR (E.symm (u, v) i))) =
      (∏ i, A i (kronLeftIndex jdx i) (u i)) *
        (∏ i, B i (kronRightIndex jdx i) (v i)) := by
    rw [Finset.prod_mul_distrib]
    congr 1
    · refine Finset.prod_congr rfl (fun i _ ↦ ?_)
      rw [hL i, kronDecodeL_eq_kronLeftIndex]
    · refine Finset.prod_congr rfl (fun i _ ↦ ?_)
      rw [hR i, kronDecodeR_eq_kronRightIndex]
  have hkl : kronLeftIndex (E.symm (u, v)) = u := by
    funext i
    exact hL i
  have hkr : kronRightIndex (E.symm (u, v)) = v := by
    funext i
    exact hR i
  rw [hKron, hkl, hkr]
  ring

section Field

universe u
variable {F : Type u} [Field F]

lemma constTensor_dsum {d₁ d₂ : Fin 3 → ℕ+} (S : T3 F d₁) (T : T3 F d₂) :
    constTensor (OM.PolMul.dsum S T) = rawDsum (constTensor S) (constTensor T) := by
  classical
  funext idx
  unfold constTensor OM.PolMul.dsum Semicontinuity.directSumTensor rawDsum
  by_cases hS : ∀ i, (idx i).val < (d₁ i : ℕ)
  · simp only [dif_pos hS]
  · by_cases hT : ∀ i, (d₁ i : ℕ) ≤ (idx i).val
    · simp only [dif_neg hS, dif_pos hT]
    · simp only [dif_neg hS, dif_neg hT, map_zero]

/-- Direct sums of polynomial arcs are polynomial arcs. -/
lemma Arc.dsum {dT₁ dS₁ dT₂ dS₂ : Fin 3 → ℕ+}
    {T₁ : T3 F dT₁} {S₁ : T3 F dS₁} {T₂ : T3 F dT₂} {S₂ : T3 F dS₂}
    (h₁ : Arc T₁ S₁) (h₂ : Arc T₂ S₂) :
    Arc (OM.PolMul.dsum T₁ T₂) (OM.PolMul.dsum S₁ S₂) := by
  classical
  rcases h₁ with ⟨q, A, E₁, hA⟩
  rcases h₂ with ⟨r, B, E₂, hB⟩
  let A' := scaleFirst (Polynomial.X ^ r) A
  let B' := scaleFirst (Polynomial.X ^ q) B
  let Q := q + r
  refine ⟨Q, blockDiag A' B', rawDsum E₁ E₂, ?_⟩
  intro idx
  rw [constTensor_dsum]
  rw [← action_blockDiag]
  have hA' (x) : action A' (constTensor S₁) x =
      Polynomial.X ^ Q * Polynomial.C (T₁ x) + Polynomial.X ^ (Q + 1) * E₁ x := by
    rw [show action A' (constTensor S₁) x =
        Polynomial.X ^ r * action A (constTensor S₁) x by
      exact action_scaleFirst _ _ _ _]
    rw [hA]
    rw [mul_add, ← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add]
    have hmain : r + q = Q := by simp only [Q]; omega
    have herr : r + (q + 1) = Q + 1 := by simp only [Q]; omega
    rw [hmain, herr]
  have hB' (x) : action B' (constTensor S₂) x =
      Polynomial.X ^ Q * Polynomial.C (T₂ x) + Polynomial.X ^ (Q + 1) * E₂ x := by
    rw [show action B' (constTensor S₂) x =
        Polynomial.X ^ q * action B (constTensor S₂) x by
      exact action_scaleFirst _ _ _ _]
    rw [hB]
    rw [mul_add, ← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add]
    have hmain : q + r = Q := rfl
    have herr : q + (r + 1) = Q + 1 := by simp only [Q]; omega
    rw [hmain, herr]
  rw [rawDsum_apply, rawDsum_apply]
  by_cases hL : ∀ i, (idx i).val < (dT₁ i : ℕ)
  · simp only [dif_pos hL]
    rw [hA']
    unfold OM.PolMul.dsum Semicontinuity.directSumTensor
    simp only [dif_pos hL]
  · by_cases hR : ∀ i, (dT₁ i : ℕ) ≤ (idx i).val
    · simp only [dif_neg hL, dif_pos hR]
      rw [hB']
      unfold OM.PolMul.dsum Semicontinuity.directSumTensor
      simp only [dif_neg hL, dif_pos hR]
    · simp only [dif_neg hL, dif_neg hR]
      unfold OM.PolMul.dsum Semicontinuity.directSumTensor
      simp only [dif_neg hL, dif_neg hR, map_zero, mul_zero, add_zero]

/-- Kronecker products of polynomial arcs are polynomial arcs. -/
lemma Arc.kron {dT₁ dS₁ dT₂ dS₂ : Fin 3 → ℕ+}
    {T₁ : T3 F dT₁} {S₁ : T3 F dS₁} {T₂ : T3 F dT₂} {S₂ : T3 F dS₂}
    (h₁ : Arc T₁ S₁) (h₂ : Arc T₂ S₂) :
    Arc (OM.PolMul.kron T₁ T₂) (OM.PolMul.kron S₁ S₂) := by
  classical
  rcases h₁ with ⟨q, A, E₁, hA⟩
  rcases h₂ with ⟨r, B, E₂, hB⟩
  let Q := q + r
  refine ⟨Q, kronMatrix A B, fun idx ↦
      Polynomial.C (T₁ (kronLeftIndex idx)) * E₂ (kronRightIndex idx) +
      E₁ (kronLeftIndex idx) * Polynomial.C (T₂ (kronRightIndex idx)) +
      Polynomial.X * E₁ (kronLeftIndex idx) * E₂ (kronRightIndex idx), ?_⟩
  intro idx
  rw [show action (kronMatrix A B) (constTensor (OM.PolMul.kron S₁ S₂)) idx =
      action A (constTensor S₁) (kronLeftIndex idx) *
        action B (constTensor S₂) (kronRightIndex idx) by
    unfold constTensor OM.PolMul.kron Semicontinuity.kroneckerTensor
    simp only [map_mul]
    exact action_kronMatrix A B (constTensor S₁) (constTensor S₂) idx]
  rw [hA, hB]
  unfold OM.PolMul.kron Semicontinuity.kroneckerTensor
  simp only [map_mul]
  simp only [Q]
  simp only [pow_add, pow_one]
  ring

end Field

end OM.PolMul.DegenerationFacts
