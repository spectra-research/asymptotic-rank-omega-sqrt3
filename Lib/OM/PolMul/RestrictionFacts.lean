/- Adapted from PolMul/RestrictionFacts.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Amanov, van den Berg and Zuiddam (2026),
   “Multiplying matrices via polynomials: exposition and barriers”.
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMul.Defs
import Lib.OM.PolMulStatements.RF_1
import Lib.OM.PolMulStatements.RF_2
import Lib.OM.PolMulStatements.RF_3
import Lib.OM.PolMulStatements.RF_4
import Lib.OM.PolMulStatements.RF_5

/-!
# Elementary restriction facts

This module proves the five parts of the lemma on restriction facts in Section 2.2.  The coordinate arguments below follow the paper: all
isomorphisms are permutation matrices induced by the displayed basis maps.
-/

namespace OM.PolMul.RestrictionFacts

open Semicontinuity
open scoped BigOperators

universe u

variable {F : Type u} [Field F]

/-- A coordinatewise bijection carrying the entries of one tensor to another
gives an isomorphism in the invertible-leg-matrix sense. -/
private lemma isoOfEquiv {dT dS : Fin 3 → ℕ+}
    (T : OM.PolMul.T3 F dT) (S : OM.PolMul.T3 F dS)
    (e : ∀ i : Fin 3, Fin (dT i) ≃ Fin (dS i))
    (h : ∀ idx, T idx = S (fun i => e i (idx i))) : OM.PolMul.Iso T S := by
  classical
  let A : ∀ i : Fin 3, Matrix (Fin (dT i)) (Fin (dS i)) F :=
    fun i x y => if e i x = y then 1 else 0
  let B : ∀ i : Fin 3, Matrix (Fin (dS i)) (Fin (dT i)) F :=
    fun i y x => if y = e i x then 1 else 0
  refine ⟨A, B, ?_, ?_, ?_⟩
  · intro i
    ext x x'
    simp only [Matrix.mul_apply, Matrix.one_apply]
    by_cases hxx : x = x'
    · subst x'
      simp [A, B]
    · have he : e i x ≠ e i x' := fun heq => hxx ((e i).injective heq)
      simp [A, B, hxx, he]
  · intro i
    ext y y'
    simp only [Matrix.mul_apply, Matrix.one_apply]
    by_cases hyy : y = y'
    · subst y'
      rw [Finset.sum_eq_single ((e i).symm y)]
      · simp [A, B]
      · intro x _ hx
        have hne : y ≠ e i x := by
          intro heq
          apply hx
          apply (e i).injective
          simpa using! heq.symm
        simp [A, B, hne]
      · simp
    · rw [if_neg hyy, Finset.sum_eq_zero]
      intro x _
      by_cases hy'x : e i x = y'
      · have hyx : y ≠ e i x := fun heq => hyy (heq.trans hy'x)
        simp [A, B, hy'x, hyx]
        exact hyy
      · simp [A, B, hy'x]
  · intro idx
    rw [h idx]
    rw [Finset.sum_eq_single (fun i => e i (idx i))]
    · simp [A]
    · intro sidx _ hsidx
      have hex : ∃ i : Fin 3, e i (idx i) ≠ sidx i := by
        by_contra hall
        push_neg at hall
        exact hsidx (funext fun i => (hall i).symm)
      obtain ⟨i, hi⟩ := hex
      have hz : A i (idx i) (sidx i) = 0 := by simp [A, hi]
      rw [show (∏ j : Fin 3, A j (idx j) (sidx j)) = 0 from
        Finset.prod_eq_zero (Finset.mem_univ i) hz, zero_mul]
    · simp

private lemma isoOfEq {d : Fin 3 → ℕ+} (T S : OM.PolMul.T3 F d)
    (h : T = S) : OM.PolMul.Iso T S := by
  subst S
  exact isoOfEquiv T T (fun _ => Equiv.refl _) (fun _ => rfl)

/-- The lemma on restriction facts (i).  This is the paper's
coordinate-selection argument, written directly for the positive unit. -/
theorem proof_RF_1 : OM_S_RF_1 := by
  intro F _ d T hT
  classical
  have hex : ∃ idx : ∀ i : Fin 3, Fin (d i), T idx ≠ 0 := by
    by_contra h
    push_neg at h
    apply hT
    funext idx
    exact h idx
  obtain ⟨idx₀, hidx₀⟩ := hex
  let i₀ : Fin 3 := 0
  refine ⟨fun i _ (c : Fin (d i)) =>
    if i = i₀ then (if c = idx₀ i then (T idx₀)⁻¹ else 0)
    else (if c = idx₀ i then 1 else 0), ?_⟩
  intro jdx
  rw [Finset.sum_eq_single idx₀]
  · have hprod :
        (∏ i : Fin 3, if i = i₀ then
            (if idx₀ i = idx₀ i then (T idx₀)⁻¹ else 0)
          else (if idx₀ i = idx₀ i then 1 else 0)) = (T idx₀)⁻¹ := by
      simp only [ite_true]
      rw [Finset.prod_ite_eq' Finset.univ i₀ (fun _ => (T idx₀)⁻¹)]
      simp
    rw [hprod, inv_mul_cancel₀ hidx₀]
    rw [show OM.PolMulDef.unit (F := F) 1 jdx = 1 by
      simp only [OM.PolMulDef.unit]
      rw [if_pos]
      intro i j
      fin_cases i <;> fin_cases j <;> simp [OM.PolMulDef.fmt]]
  · intro idx _ hne
    have hleg : ∃ i : Fin 3, idx i ≠ idx₀ i := by
      by_contra h
      push_neg at h
      exact hne (funext h)
    obtain ⟨i, hi⟩ := hleg
    apply mul_eq_zero_of_left
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    by_cases hii₀ : i = i₀ <;> simp [hii₀, hi]
  · simp

private lemma unitRestrictsEquivUnitTensor (r : ℕ+) :
    RestrictsEquiv (OM.PolMul.unit (F := F) r)
      (unitTensor F (k := 3) r) := by
  constructor
  · apply Restricts.of_eq_cast
      (fun i => by fin_cases i <;> rfl)
    intro idx
    simp only [OM.PolMul.unit, unitTensor]
    congr 1
    apply propext
    simp only [Fin.ext_iff, Fin.val_cast]
  · apply Restricts.of_eq_cast
      (fun i => by fin_cases i <;> rfl)
    intro idx
    simp only [OM.PolMul.unit, unitTensor]
    congr 1
    apply propext
    simp only [Fin.ext_iff, Fin.val_cast]

/-- The diagonal tensor has its evident decomposition into `r` simple tensors. -/
private lemma tensorRank_unit_le (r : ℕ+) :
    Semicontinuity.tensorRank (OM.PolMul.unit (F := F) r) ≤ (r : ℕ) := by
  classical
  unfold Semicontinuity.tensorRank
  apply Nat.sInf_le
  refine ⟨fun c => simpleTensor (F := F)
      (fun _ j => if j.val = c.val then 1 else 0), ?_, ?_⟩
  · intro c
    exact ⟨_, rfl⟩
  · funext idx
    simp only [OM.PolMul.unit, Finset.sum_apply, simpleTensor]
    by_cases hdiag : ∀ i j : Fin 3, (idx i).val = (idx j).val
    · rw [if_pos hdiag, Finset.sum_eq_single
          (⟨(idx 0).val, by simpa [OM.PolMul.fmt] using! (idx 0).isLt⟩ : Fin (r : ℕ))]
      · symm
        apply Finset.prod_eq_one
        intro i _
        rw [if_pos]
        exact hdiag i 0
      · intro c _ hc
        have hne : (idx 0).val ≠ c.val := by
          intro heq
          apply hc
          exact Fin.ext heq.symm
        rw [Finset.prod_eq_zero (Finset.mem_univ (0 : Fin 3))]
        simp [hne]
      · simp
    · rw [if_neg hdiag, Finset.sum_eq_zero]
      intro c _
      have hex : ∃ i : Fin 3, (idx i).val ≠ c.val := by
        by_contra h
        push_neg at h
        apply hdiag
        intro i j
        exact (h i).trans (h j).symm
      obtain ⟨i, hi⟩ := hex
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- A rank decomposition gives a restriction to the diagonal tensor of the
same (positive) size. -/
private lemma restricts_unitTensor_tensorRank {d : Fin 3 → ℕ+}
    (T : OM.PolMul.T3 F d) (hT : T ≠ 0) :
    Restricts T (unitTensor F (k := 3)
      ⟨Semicontinuity.tensorRank T, by
        by_contra hr
        simp only [Nat.not_lt, Nat.le_zero] at hr
        have hmem : Semicontinuity.tensorRank T ∈
            {n : ℕ | ∃ s : Fin n → KTensor F d,
              (∀ i, IsSimpleTensor (s i)) ∧ T = ∑ i, s i} := by
          apply Nat.sInf_mem
          exact exists_tensorRank_decomp (by norm_num) T
        rw [hr] at hmem
        obtain ⟨s, _, hs⟩ := hmem
        apply hT
        simpa using! hs⟩) := by
  classical
  let R := Semicontinuity.tensorRank T
  have hmem : R ∈ {n : ℕ | ∃ s : Fin n → KTensor F d,
      (∀ i, IsSimpleTensor (s i)) ∧ T = ∑ i, s i} := by
    apply Nat.sInf_mem
    exact exists_tensorRank_decomp (by norm_num) T
  obtain ⟨s, hs, hsum⟩ := hmem
  choose u hu using hs
  refine ⟨fun i row c => u c i row, ?_⟩
  intro idx
  have hsum' : T idx = ∑ c : Fin R, ∏ i : Fin 3, u c i (idx i) := by
    rw [hsum, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro c _
    rw [hu c]
    rfl
  rw [hsum']
  refine Finset.sum_of_injOn
    (e := fun c : Fin R => (fun _ : Fin 3 => c)) ?_ ?_ ?_ ?_
  · intro a _ b _ hab
    exact congrFun hab 0
  · intro c _
    exact Finset.mem_univ _
  · intro sidx _ hnot
    have hnconst : ¬ ∀ i j : Fin 3, sidx i = sidx j := by
      intro hall
      apply hnot
      refine ⟨sidx 0, by simp, ?_⟩
      funext i
      exact (hall i 0).symm
    simp [unitTensor, hnconst]
  · intro c _
    simp [unitTensor]

/-- The lemma on restriction facts (ii).  The forward direction
uses the least simple-tensor decomposition; the reverse direction is rank
monotonicity under restriction, exactly as in the cited characterisation. -/
theorem proof_RF_2 : OM_S_RF_2 := by
  intro F _ d T
  refine ⟨?_, fun r => ?_⟩
  · change Semicontinuity.tensorRank T = 0 ↔ T = 0
    constructor
    · intro hr
      have hmem : Semicontinuity.tensorRank T ∈
          {n : ℕ | ∃ s : Fin n → KTensor F d,
            (∀ i, IsSimpleTensor (s i)) ∧ T = ∑ i, s i} := by
        apply Nat.sInf_mem
        exact exists_tensorRank_decomp (by norm_num) T
      rw [hr] at hmem
      obtain ⟨s, _, hs⟩ := hmem
      simpa using! hs
    · intro hT
      subst T
      exact tensorRank_zero
  · change OM.PolMul.tensorRank T ≤ (r : ℕ) ↔
      Restricts T (OM.PolMul.unit (F := F) r)
    constructor
    · intro hr
      by_cases hT : T = 0
      · subst T
        exact ⟨fun _ => 0, by
          intro idx
          simp only [Pi.zero_apply]
          symm
          apply Finset.sum_eq_zero
          intro sidx _
          rw [Finset.prod_eq_zero (Finset.mem_univ (0 : Fin 3)) rfl, zero_mul]⟩
      · let q : ℕ+ := ⟨Semicontinuity.tensorRank T, by
            by_contra h
            simp only [Nat.not_lt, Nat.le_zero] at h
            have hmem : Semicontinuity.tensorRank T ∈
                {n : ℕ | ∃ s : Fin n → KTensor F d,
                  (∀ i, IsSimpleTensor (s i)) ∧ T = ∑ i, s i} := by
              apply Nat.sInf_mem
              exact exists_tensorRank_decomp (by norm_num) T
            rw [h] at hmem
            obtain ⟨s, _, hs⟩ := hmem
            apply hT
            simpa using! hs⟩
        have h₁ : Restricts T (unitTensor F (k := 3) q) := by
          simpa [q] using! restricts_unitTensor_tensorRank T hT
        have h₂ : Restricts (unitTensor F (k := 3) q)
            (unitTensor F (k := 3) r) :=
          unitTensor_restricts_of_le hr
        exact h₁.trans (h₂.trans (unitRestrictsEquivUnitTensor r).2)
    · intro h
      change Semicontinuity.tensorRank T ≤ (r : ℕ)
      exact (tensorRank_mono_under_Restricts (by norm_num) h).trans
        (tensorRank_unit_le r)

private def prodShuffle (A B C D : Type*) :
    (A × B) × (C × D) ≃ (A × C) × (B × D) where
  toFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  invFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Regroup two paired coordinates as `(a,b),(c,d) ↦ (a,c),(b,d)`. -/
private def mulShuffle (a b c d : ℕ+) :
    Fin ((a * b) * (c * d) : ℕ+) ≃ Fin ((a * c) * (b * d) : ℕ+) :=
  (kronDecodeEquiv (d₁ := a * b) (d₂ := c * d)).trans
    (((kronDecodeEquiv (d₁ := a) (d₂ := b)).prodCongr
      (kronDecodeEquiv (d₁ := c) (d₂ := d))).trans
    ((prodShuffle (Fin a) (Fin b) (Fin c) (Fin d)).trans
    ((((kronDecodeEquiv (d₁ := a) (d₂ := c)).symm).prodCongr
      (kronDecodeEquiv (d₁ := b) (d₂ := d)).symm).trans
      (kronDecodeEquiv (d₁ := a * c) (d₂ := b * d)).symm)))

private lemma mulShuffle_spec (a b c d : ℕ+)
    (x : Fin ((a * b) * (c * d) : ℕ+)) :
    let z := kronDecodeEquiv (d₁ := a * c) (d₂ := b * d)
      (mulShuffle a b c d x)
    let ab := kronDecodeEquiv (d₁ := a) (d₂ := b) (kronDecodeL x)
    let cd := kronDecodeEquiv (d₁ := c) (d₂ := d) (kronDecodeR x)
    kronDecodeEquiv (d₁ := a) (d₂ := c) z.1 = (ab.1, cd.1) ∧
      kronDecodeEquiv (d₁ := b) (d₂ := d) z.2 = (ab.2, cd.2) := by
  simp [mulShuffle, prodShuffle, kronDecodeL, kronDecodeR, kronDecodeEquiv]

private lemma matMul_apply_decode (a b c : ℕ+)
    (idx : ∀ i : Fin 3,
      Fin (OM.PolMul.fmt (a * b) (b * c) (c * a) i)) :
    OM.PolMul.matMul (F := F) a b c idx =
      if (kronDecodeEquiv (d₁ := a) (d₂ := b) (idx 0)).2 =
          (kronDecodeEquiv (d₁ := b) (d₂ := c) (idx 1)).1 ∧
        (kronDecodeEquiv (d₁ := b) (d₂ := c) (idx 1)).2 =
          (kronDecodeEquiv (d₁ := c) (d₂ := a) (idx 2)).1 ∧
        (kronDecodeEquiv (d₁ := c) (d₂ := a) (idx 2)).2 =
          (kronDecodeEquiv (d₁ := a) (d₂ := b) (idx 0)).1
      then 1 else 0 := rfl

/-- The lemma on restriction facts (iii).  This directly
formalises the paper's basis map
`Eᵢⱼ ⊗ Eₖₗ ↦ E₍ᵢ₌ₖ₎,₍ⱼ₌ₗ₎` on each leg. -/
theorem proof_RF_3 : OM_S_RF_3 := by
  intro F _ n₁ n₂ n₃ m₁ m₂ m₃
  change OM.PolMul.Iso
    (OM.PolMul.kron (OM.PolMul.matMul (F := F) n₁ n₂ n₃)
      (OM.PolMul.matMul m₁ m₂ m₃))
    (OM.PolMul.matMul (n₁ * m₁) (n₂ * m₂) (n₃ * m₃))
  let e : ∀ i : Fin 3,
      Fin (((OM.PolMul.fmt (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) i) *
        (OM.PolMul.fmt (m₁ * m₂) (m₂ * m₃) (m₃ * m₁) i) : ℕ+) : ℕ) ≃
      Fin (OM.PolMul.fmt ((n₁ * m₁) * (n₂ * m₂))
        ((n₂ * m₂) * (n₃ * m₃))
        ((n₃ * m₃) * (n₁ * m₁)) i) := fun
    | 0 => mulShuffle n₁ n₂ m₁ m₂
    | 1 => mulShuffle n₂ n₃ m₂ m₃
    | 2 => mulShuffle n₃ n₁ m₃ m₁
  apply isoOfEquiv _ _ e
  intro idx
  simp only [OM.PolMul.kron, kroneckerTensor, matMul_apply_decode]
  have h₀ := mulShuffle_spec n₁ n₂ m₁ m₂ (idx 0)
  have h₁ := mulShuffle_spec n₂ n₃ m₂ m₃ (idx 1)
  have h₂ := mulShuffle_spec n₃ n₁ m₃ m₁ (idx 2)
  dsimp only [e] at h₀ h₁ h₂ ⊢
  have hp :
      (kronDecodeEquiv (d₁ := n₁ * m₁) (d₂ := n₂ * m₂)
          (mulShuffle n₁ n₂ m₁ m₂ (idx 0))).2 =
        (kronDecodeEquiv (d₁ := n₂ * m₂) (d₂ := n₃ * m₃)
          (mulShuffle n₂ n₃ m₂ m₃ (idx 1))).1 ↔
      (kronDecodeEquiv (d₁ := n₁) (d₂ := n₂) (kronLeftIndex idx 0)).2 =
          (kronDecodeEquiv (d₁ := n₂) (d₂ := n₃) (kronLeftIndex idx 1)).1 ∧
        (kronDecodeEquiv (d₁ := m₁) (d₂ := m₂) (kronRightIndex idx 0)).2 =
          (kronDecodeEquiv (d₁ := m₂) (d₂ := m₃) (kronRightIndex idx 1)).1 := by
    rw [← (kronDecodeEquiv (d₁ := n₂) (d₂ := m₂)).injective.eq_iff,
      h₀.2, h₁.1]
    simp only [Prod.mk.injEq, kronDecodeL_eq_kronLeftIndex,
      kronDecodeR_eq_kronRightIndex]
  have hq :
      (kronDecodeEquiv (d₁ := n₂ * m₂) (d₂ := n₃ * m₃)
          (mulShuffle n₂ n₃ m₂ m₃ (idx 1))).2 =
        (kronDecodeEquiv (d₁ := n₃ * m₃) (d₂ := n₁ * m₁)
          (mulShuffle n₃ n₁ m₃ m₁ (idx 2))).1 ↔
      (kronDecodeEquiv (d₁ := n₂) (d₂ := n₃) (kronLeftIndex idx 1)).2 =
          (kronDecodeEquiv (d₁ := n₃) (d₂ := n₁) (kronLeftIndex idx 2)).1 ∧
        (kronDecodeEquiv (d₁ := m₂) (d₂ := m₃) (kronRightIndex idx 1)).2 =
          (kronDecodeEquiv (d₁ := m₃) (d₂ := m₁) (kronRightIndex idx 2)).1 := by
    rw [← (kronDecodeEquiv (d₁ := n₃) (d₂ := m₃)).injective.eq_iff,
      h₁.2, h₂.1]
    simp only [Prod.mk.injEq, kronDecodeL_eq_kronLeftIndex,
      kronDecodeR_eq_kronRightIndex]
  have hr :
      (kronDecodeEquiv (d₁ := n₃ * m₃) (d₂ := n₁ * m₁)
          (mulShuffle n₃ n₁ m₃ m₁ (idx 2))).2 =
        (kronDecodeEquiv (d₁ := n₁ * m₁) (d₂ := n₂ * m₂)
          (mulShuffle n₁ n₂ m₁ m₂ (idx 0))).1 ↔
      (kronDecodeEquiv (d₁ := n₃) (d₂ := n₁) (kronLeftIndex idx 2)).2 =
          (kronDecodeEquiv (d₁ := n₁) (d₂ := n₂) (kronLeftIndex idx 0)).1 ∧
        (kronDecodeEquiv (d₁ := m₃) (d₂ := m₁) (kronRightIndex idx 2)).2 =
          (kronDecodeEquiv (d₁ := m₁) (d₂ := m₂) (kronRightIndex idx 0)).1 := by
    rw [← (kronDecodeEquiv (d₁ := n₁) (d₂ := m₁)).injective.eq_iff,
      h₂.2, h₀.1]
    simp only [Prod.mk.injEq, kronDecodeL_eq_kronLeftIndex,
      kronDecodeR_eq_kronRightIndex]
  let l₀ : Prop :=
    (kronDecodeEquiv (d₁ := n₁) (d₂ := n₂) (kronLeftIndex idx 0)).2 =
      (kronDecodeEquiv (d₁ := n₂) (d₂ := n₃) (kronLeftIndex idx 1)).1
  let l₁ : Prop :=
    (kronDecodeEquiv (d₁ := n₂) (d₂ := n₃) (kronLeftIndex idx 1)).2 =
      (kronDecodeEquiv (d₁ := n₃) (d₂ := n₁) (kronLeftIndex idx 2)).1
  let l₂ : Prop :=
    (kronDecodeEquiv (d₁ := n₃) (d₂ := n₁) (kronLeftIndex idx 2)).2 =
      (kronDecodeEquiv (d₁ := n₁) (d₂ := n₂) (kronLeftIndex idx 0)).1
  let r₀ : Prop :=
    (kronDecodeEquiv (d₁ := m₁) (d₂ := m₂) (kronRightIndex idx 0)).2 =
      (kronDecodeEquiv (d₁ := m₂) (d₂ := m₃) (kronRightIndex idx 1)).1
  let r₁ : Prop :=
    (kronDecodeEquiv (d₁ := m₂) (d₂ := m₃) (kronRightIndex idx 1)).2 =
      (kronDecodeEquiv (d₁ := m₃) (d₂ := m₁) (kronRightIndex idx 2)).1
  let r₂ : Prop :=
    (kronDecodeEquiv (d₁ := m₃) (d₂ := m₁) (kronRightIndex idx 2)).2 =
      (kronDecodeEquiv (d₁ := m₁) (d₂ := m₂) (kronRightIndex idx 0)).1
  let a₀ : Prop :=
    (kronDecodeEquiv (d₁ := n₁ * m₁) (d₂ := n₂ * m₂)
        (mulShuffle n₁ n₂ m₁ m₂ (idx 0))).2 =
      (kronDecodeEquiv (d₁ := n₂ * m₂) (d₂ := n₃ * m₃)
        (mulShuffle n₂ n₃ m₂ m₃ (idx 1))).1
  let a₁ : Prop :=
    (kronDecodeEquiv (d₁ := n₂ * m₂) (d₂ := n₃ * m₃)
        (mulShuffle n₂ n₃ m₂ m₃ (idx 1))).2 =
      (kronDecodeEquiv (d₁ := n₃ * m₃) (d₂ := n₁ * m₁)
        (mulShuffle n₃ n₁ m₃ m₁ (idx 2))).1
  let a₂ : Prop :=
    (kronDecodeEquiv (d₁ := n₃ * m₃) (d₂ := n₁ * m₁)
        (mulShuffle n₃ n₁ m₃ m₁ (idx 2))).2 =
      (kronDecodeEquiv (d₁ := n₁ * m₁) (d₂ := n₂ * m₂)
        (mulShuffle n₁ n₂ m₁ m₂ (idx 0))).1
  change (if l₀ ∧ l₁ ∧ l₂ then 1 else 0) *
      (if r₀ ∧ r₁ ∧ r₂ then 1 else 0) =
    if a₀ ∧ a₁ ∧ a₂ then 1 else 0
  have hp' : a₀ ↔ l₀ ∧ r₀ := hp
  have hq' : a₁ ↔ l₁ ∧ r₁ := hq
  have hr' : a₂ ↔ l₂ ∧ r₂ := hr
  have hall : a₀ ∧ a₁ ∧ a₂ ↔
      (l₀ ∧ l₁ ∧ l₂) ∧ (r₀ ∧ r₁ ∧ r₂) := by
    aesop
  by_cases ha : a₀ ∧ a₁ ∧ a₂
  · obtain ⟨hl, hr⟩ := hall.mp ha
    simp [ha, hl, hr]
  · have hnot : ¬ ((l₀ ∧ l₁ ∧ l₂) ∧ (r₀ ∧ r₁ ∧ r₂)) :=
      fun h => ha (hall.mpr h)
    by_cases hl : l₀ ∧ l₁ ∧ l₂
    · have hr : ¬ (r₀ ∧ r₁ ∧ r₂) := fun h => hnot ⟨hl, h⟩
      simp [ha, hl, hr]
    · simp [ha, hl]

private lemma unit_one_apply
    (idx : ∀ i : Fin 3, Fin (OM.PolMul.fmt 1 1 1 i)) :
    OM.PolMul.unit (F := F) 1 idx = 1 := by
  simp only [OM.PolMul.unit]
  rw [if_pos]
  intro i j
  fin_cases i <;> fin_cases j <;> simp [OM.PolMul.fmt]

/-- The lemma on restriction facts (iv).  The three commuting
identities and restriction transport are the dependency's leg-reindexing
lemmas; `Iso` is supplied by the corresponding permutation matrices. -/
theorem proof_RF_4 : OM_S_RF_4 := by
  intro F _ π dS dT S T
  change OM.PolMul.Iso (OM.PolMul.perm π (OM.PolMul.dsum S T))
        (OM.PolMul.dsum (OM.PolMul.perm π S) (OM.PolMul.perm π T)) ∧
      OM.PolMul.Iso (OM.PolMul.perm π (OM.PolMul.kron S T))
        (OM.PolMul.kron (OM.PolMul.perm π S) (OM.PolMul.perm π T)) ∧
      OM.PolMul.Iso (OM.PolMul.perm π (OM.PolMul.unit (F := F) 1)) (OM.PolMul.unit 1) ∧
      (Restricts T S → Restricts (OM.PolMul.perm π T) (OM.PolMul.perm π S))
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply isoOfEq
    simpa only [OM.PolMul.perm, OM.PolMul.dsum] using!
      (KTensor.legReindex_directSum π.symm S T)
  · apply isoOfEq
    simpa only [OM.PolMul.perm, OM.PolMul.kron] using!
      (KTensor.legReindex_kron π.symm S T)
  · have hunit : ∀ j : Fin 3, OM.PolMul.fmt 1 1 1 j = 1 := by
      intro j
      fin_cases j <;> rfl
    let e : ∀ i : Fin 3,
        Fin ((OM.PolMul.fmt 1 1 1 ∘ π.symm) i) ≃ Fin (OM.PolMul.fmt 1 1 1 i) :=
      fun i => finCongr (congrArg PNat.val
        ((hunit (π.symm i)).trans (hunit i).symm))
    apply isoOfEquiv _ _ e
    intro idx
    change OM.PolMul.unit (F := F) 1 _ = OM.PolMul.unit 1 _
    rw [unit_one_apply, unit_one_apply]
  · intro h
    simpa only [OM.PolMul.perm] using! KTensor.legReindex_Restricts π.symm h

private def pairSwap (a b : ℕ+) : Fin (a * b : ℕ+) ≃ Fin (b * a : ℕ+) :=
  (kronDecodeEquiv (d₁ := a) (d₂ := b)).trans
    ((Equiv.prodComm _ _).trans (kronDecodeEquiv (d₁ := b) (d₂ := a)).symm)

private lemma pairSwap_spec (a b : ℕ+) (x : Fin (a * b : ℕ+)) :
    kronDecodeEquiv (d₁ := b) (d₂ := a) (pairSwap a b x) =
      ((kronDecodeEquiv (d₁ := a) (d₂ := b) x).2,
       (kronDecodeEquiv (d₁ := a) (d₂ := b) x).1) := by
  simp only [pairSwap, Equiv.trans_apply, Equiv.prodComm_apply,
    Equiv.apply_symm_apply]
  cases kronDecodeEquiv (d₁ := a) (d₂ := b) x
  rfl

private lemma iso_rotate_matMul (n₁ n₂ n₃ : ℕ+) :
    OM.PolMul.Iso
      (OM.PolMul.perm (finRotate 3) (OM.PolMul.matMul (F := F) n₁ n₂ n₃))
      (OM.PolMul.matMul n₃ n₁ n₂) := by
  let e : ∀ i : Fin 3,
      Fin ((OM.PolMul.fmt (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) ∘
        (finRotate 3).symm) i) ≃
      Fin (OM.PolMul.fmt (n₃ * n₁) (n₁ * n₂) (n₂ * n₃) i) :=
    fun i => finCongr (congrArg PNat.val (by
      fin_cases i <;> simp [OM.PolMul.fmt] <;> rfl))
  apply isoOfEquiv _ _ e
  intro idx
  simp only [OM.PolMul.perm, KTensor.legReindex, matMul_apply_decode]
  dsimp only [e]
  congr 1
  apply propext
  simp only [Fin.ext_iff, finProdFinEquiv_symm_apply, Fin.coe_divNat,
    Fin.coe_modNat, Fin.val_cast, piCongrLeft_val]
  constructor <;> aesop

private lemma iso_rotate_symm_matMul (n₁ n₂ n₃ : ℕ+) :
    OM.PolMul.Iso
      (OM.PolMul.perm (finRotate 3)⁻¹ (OM.PolMul.matMul (F := F) n₁ n₂ n₃))
      (OM.PolMul.matMul n₂ n₃ n₁) := by
  change OM.PolMul.Iso
    (OM.PolMul.perm (finRotate 3).symm (OM.PolMul.matMul (F := F) n₁ n₂ n₃))
    (OM.PolMul.matMul n₂ n₃ n₁)
  let e : ∀ i : Fin 3,
      Fin ((OM.PolMul.fmt (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) ∘
        (finRotate 3).symm.symm) i) ≃
      Fin (OM.PolMul.fmt (n₂ * n₃) (n₃ * n₁) (n₁ * n₂) i) :=
    fun i => finCongr (congrArg PNat.val (by
      fin_cases i <;> simp [OM.PolMul.fmt]))
  apply isoOfEquiv _ _ e
  intro idx
  simp only [OM.PolMul.perm, KTensor.legReindex, matMul_apply_decode]
  dsimp only [e]
  congr 1
  apply propext
  simp only [Fin.ext_iff, finProdFinEquiv_symm_apply, Fin.coe_divNat,
    Fin.coe_modNat, Fin.val_cast, piCongrLeft_val]
  constructor <;> aesop

private lemma iso_swap01_matMul (n₁ n₂ n₃ : ℕ+) :
    OM.PolMul.Iso
      (OM.PolMul.perm (Equiv.swap 0 1) (OM.PolMul.matMul (F := F) n₁ n₂ n₃))
      (OM.PolMul.matMul n₃ n₂ n₁) := by
  let e : ∀ i : Fin 3,
      Fin ((OM.PolMul.fmt (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) ∘
        (Equiv.swap 0 1).symm) i) ≃
      Fin (OM.PolMul.fmt (n₃ * n₂) (n₂ * n₁) (n₁ * n₃) i) := fun
    | 0 => pairSwap n₂ n₃
    | 1 => pairSwap n₁ n₂
    | 2 => pairSwap n₃ n₁
  apply isoOfEquiv _ _ e
  intro idx
  simp only [OM.PolMul.perm, KTensor.legReindex, matMul_apply_decode]
  have h₀ := pairSwap_spec n₂ n₃ (idx 0)
  have h₁ := pairSwap_spec n₁ n₂ (idx 1)
  have h₂ := pairSwap_spec n₃ n₁ (idx 2)
  dsimp only [e] at h₀ h₁ h₂ ⊢
  have h₀l := congrArg Prod.fst h₀
  have h₀r := congrArg Prod.snd h₀
  have h₁l := congrArg Prod.fst h₁
  have h₁r := congrArg Prod.snd h₁
  have h₂l := congrArg Prod.fst h₂
  have h₂r := congrArg Prod.snd h₂
  simp only at h₀l h₀r h₁l h₁r h₂l h₂r
  let jdx := Equiv.piCongrLeft
    (fun i => Fin (OM.PolMul.fmt (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) i))
    (Equiv.swap 0 1) idx
  have hj₀ : jdx 0 = idx 1 := by
    apply Fin.ext
    rw [piCongrLeft_val]
    simp [Equiv.swap_apply_def]
  have hj₁ : jdx 1 = idx 0 := by
    apply Fin.ext
    rw [piCongrLeft_val]
    simp [Equiv.swap_apply_def]
  have hj₂ : jdx 2 = idx 2 := by
    apply Fin.ext
    rw [piCongrLeft_val]
    simp [Equiv.swap_apply_def]
  congr 1
  apply propext
  change
    ((kronDecodeEquiv (jdx 0)).2 = (kronDecodeEquiv (jdx 1)).1 ∧
      (kronDecodeEquiv (jdx 1)).2 = (kronDecodeEquiv (jdx 2)).1 ∧
      (kronDecodeEquiv (jdx 2)).2 = (kronDecodeEquiv (jdx 0)).1) ↔ _
  rw [hj₀, hj₁, hj₂]
  constructor
  · rintro ⟨ha, hb, hc⟩
    exact ⟨h₀r.trans (ha.symm.trans h₁l.symm),
      h₁r.trans (hc.symm.trans h₂l.symm),
      h₂r.trans (hb.symm.trans h₀l.symm)⟩
  · rintro ⟨ha, hb, hc⟩
    exact ⟨h₁l.symm.trans (ha.symm.trans h₀r),
      h₀l.symm.trans (hc.symm.trans h₂r),
      h₂l.symm.trans (hb.symm.trans h₁r)⟩

private lemma iso_swap02_matMul (n₁ n₂ n₃ : ℕ+) :
    OM.PolMul.Iso
      (OM.PolMul.perm (Equiv.swap 0 2) (OM.PolMul.matMul (F := F) n₁ n₂ n₃))
      (OM.PolMul.matMul n₁ n₃ n₂) := by
  let e : ∀ i : Fin 3,
      Fin ((OM.PolMul.fmt (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) ∘
        (Equiv.swap 0 2).symm) i) ≃
      Fin (OM.PolMul.fmt (n₁ * n₃) (n₃ * n₂) (n₂ * n₁) i) := fun
    | 0 => pairSwap n₃ n₁
    | 1 => pairSwap n₂ n₃
    | 2 => pairSwap n₁ n₂
  apply isoOfEquiv _ _ e
  intro idx
  simp only [OM.PolMul.perm, KTensor.legReindex, matMul_apply_decode]
  have h₀ := pairSwap_spec n₃ n₁ (idx 0)
  have h₁ := pairSwap_spec n₂ n₃ (idx 1)
  have h₂ := pairSwap_spec n₁ n₂ (idx 2)
  dsimp only [e] at h₀ h₁ h₂ ⊢
  have h₀l := congrArg Prod.fst h₀
  have h₀r := congrArg Prod.snd h₀
  have h₁l := congrArg Prod.fst h₁
  have h₁r := congrArg Prod.snd h₁
  have h₂l := congrArg Prod.fst h₂
  have h₂r := congrArg Prod.snd h₂
  simp only at h₀l h₀r h₁l h₁r h₂l h₂r
  let jdx := Equiv.piCongrLeft
    (fun i => Fin (OM.PolMul.fmt (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) i))
    (Equiv.swap 0 2) idx
  have hj₀ : jdx 0 = idx 2 := by
    apply Fin.ext
    rw [piCongrLeft_val]
    simp [Equiv.swap_apply_def]
  have hj₁ : jdx 1 = idx 1 := by
    apply Fin.ext
    rw [piCongrLeft_val]
    simp [Equiv.swap_apply_def]
  have hj₂ : jdx 2 = idx 0 := by
    apply Fin.ext
    rw [piCongrLeft_val]
    simp [Equiv.swap_apply_def]
  congr 1
  apply propext
  change
    ((kronDecodeEquiv (jdx 0)).2 = (kronDecodeEquiv (jdx 1)).1 ∧
      (kronDecodeEquiv (jdx 1)).2 = (kronDecodeEquiv (jdx 2)).1 ∧
      (kronDecodeEquiv (jdx 2)).2 = (kronDecodeEquiv (jdx 0)).1) ↔ _
  rw [hj₀, hj₁, hj₂]
  constructor
  · rintro ⟨ha, hb, hc⟩
    exact ⟨h₀r.trans (hb.symm.trans h₁l.symm),
      h₁r.trans (ha.symm.trans h₂l.symm),
      h₂r.trans (hc.symm.trans h₀l.symm)⟩
  · rintro ⟨ha, hb, hc⟩
    exact ⟨h₂l.symm.trans (hb.symm.trans h₁r),
      h₁l.symm.trans (ha.symm.trans h₀r),
      h₀l.symm.trans (hc.symm.trans h₂r)⟩

private lemma iso_swap12_matMul (n₁ n₂ n₃ : ℕ+) :
    OM.PolMul.Iso
      (OM.PolMul.perm (Equiv.swap 1 2) (OM.PolMul.matMul (F := F) n₁ n₂ n₃))
      (OM.PolMul.matMul n₂ n₁ n₃) := by
  let e : ∀ i : Fin 3,
      Fin ((OM.PolMul.fmt (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) ∘
        (Equiv.swap 1 2).symm) i) ≃
      Fin (OM.PolMul.fmt (n₂ * n₁) (n₁ * n₃) (n₃ * n₂) i) := fun
    | 0 => pairSwap n₁ n₂
    | 1 => pairSwap n₃ n₁
    | 2 => pairSwap n₂ n₃
  apply isoOfEquiv _ _ e
  intro idx
  simp only [OM.PolMul.perm, KTensor.legReindex, matMul_apply_decode]
  have h₀ := pairSwap_spec n₁ n₂ (idx 0)
  have h₁ := pairSwap_spec n₃ n₁ (idx 1)
  have h₂ := pairSwap_spec n₂ n₃ (idx 2)
  dsimp only [e] at h₀ h₁ h₂ ⊢
  have h₀l := congrArg Prod.fst h₀
  have h₀r := congrArg Prod.snd h₀
  have h₁l := congrArg Prod.fst h₁
  have h₁r := congrArg Prod.snd h₁
  have h₂l := congrArg Prod.fst h₂
  have h₂r := congrArg Prod.snd h₂
  simp only at h₀l h₀r h₁l h₁r h₂l h₂r
  let jdx := Equiv.piCongrLeft
    (fun i => Fin (OM.PolMul.fmt (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) i))
    (Equiv.swap 1 2) idx
  have hj₀ : jdx 0 = idx 0 := by
    apply Fin.ext
    rw [piCongrLeft_val]
    simp [Equiv.swap_apply_def]
  have hj₁ : jdx 1 = idx 2 := by
    apply Fin.ext
    rw [piCongrLeft_val]
    simp [Equiv.swap_apply_def]
  have hj₂ : jdx 2 = idx 1 := by
    apply Fin.ext
    rw [piCongrLeft_val]
    simp [Equiv.swap_apply_def]
  congr 1
  apply propext
  change
    ((kronDecodeEquiv (jdx 0)).2 = (kronDecodeEquiv (jdx 1)).1 ∧
      (kronDecodeEquiv (jdx 1)).2 = (kronDecodeEquiv (jdx 2)).1 ∧
      (kronDecodeEquiv (jdx 2)).2 = (kronDecodeEquiv (jdx 0)).1) ↔ _
  rw [hj₀, hj₁, hj₂]
  constructor
  · rintro ⟨ha, hb, hc⟩
    exact ⟨h₀r.trans (hc.symm.trans h₁l.symm),
      h₁r.trans (hb.symm.trans h₂l.symm),
      h₂r.trans (ha.symm.trans h₀l.symm)⟩
  · rintro ⟨ha, hb, hc⟩
    exact ⟨h₀l.symm.trans (hc.symm.trans h₂r),
      h₂l.symm.trans (hb.symm.trans h₁r),
      h₁l.symm.trans (ha.symm.trans h₀r)⟩

/-! The sixfold symmetrisation is regrouped by parity.  The following finite
coordinate model makes the paper's “three cyclic factors times three
transposed factors” argument explicit. -/

private def permSix : Fin 6 → Equiv.Perm (Fin 3)
  | 0 => 1
  | 1 => finRotate 3
  | 2 => (finRotate 3)⁻¹
  | 3 => Equiv.swap 0 1
  | 4 => Equiv.swap 0 2
  | 5 => Equiv.swap 1 2

private lemma permSix_bijective : Function.Bijective permSix := by
  decide +kernel

private noncomputable def permSixEquiv : Fin 6 ≃ Equiv.Perm (Fin 3) :=
  Equiv.ofBijective permSix permSix_bijective

private def nextThree : Fin 3 → Fin 3
  | 0 => 1
  | 1 => 2
  | 2 => 0

private def parameterDim (n₁ n₂ n₃ : ℕ+) : Fin 3 → ℕ+
  | 0 => n₁
  | 1 => n₂
  | 2 => n₃

private def edgeDim (n₁ n₂ n₃ : ℕ+) (j : Fin 3) : ℕ+ :=
  parameterDim n₁ n₂ n₃ j * parameterDim n₁ n₂ n₃ (nextThree j)

private lemma edgeDim_eq_fmt (n₁ n₂ n₃ : ℕ+) :
    edgeDim n₁ n₂ n₃ = OM.PolMul.fmt (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) := by
  funext j
  fin_cases j <;> rfl

private def edgeParameter (j : Fin 3) : Fin 2 → Fin 3
  | 0 => j
  | 1 => nextThree j

private def edgeCoordinateEquiv (n₁ n₂ n₃ : ℕ+) (j : Fin 3) :
    Fin (edgeDim n₁ n₂ n₃ j) ≃
      ∀ t : Fin 2, Fin (parameterDim n₁ n₂ n₃ (edgeParameter j t)) :=
  (kronDecodeEquiv
      (d₁ := parameterDim n₁ n₂ n₃ j)
      (d₂ := parameterDim n₁ n₂ n₃ (nextThree j))).trans
    (piFinTwoEquiv
      (fun t => Fin (parameterDim n₁ n₂ n₃ (edgeParameter j t)))).symm

private noncomputable def splitCoordinateEquiv {ι : Type*} [Fintype ι]
    (d : ι → ℕ+) : Fin (∏ i, d i) ≃ ∀ i, Fin (d i) := by
  classical
  exact (finCongr (by
      rw [Fintype.card_pi]
      simpa only [Fintype.card_fin] using!
        (map_prod PNat.coeMonoidHom d Finset.univ).symm)).trans
      (Fintype.equivFin (∀ i, Fin (d i))).symm

private def piProdEquiv {α β : Type*} (P : α → β → Type*) :
    (∀ a b, P a b) ≃ ∀ x : α × β, P x.1 x.2 where
  toFun f x := f x.1 x.2
  invFun f a b := f (a, b)
  left_inv _ := rfl
  right_inv _ := rfl

private def sourceParameter (i : Fin 3) (x : Fin 6 × Fin 2) : Fin 3 :=
  edgeParameter ((permSix x.1).symm i) x.2

private def slotMap (i : Fin 3) (x : Fin 6 × Fin 2) :
    (Fin 2 × Fin 2) × Fin 3 :=
  let even : Bool := decide (x.1.val < 3)
  let copy : Fin 2 := if even then 0 else 1
  let endpoint : Fin 2 := if even then x.2 else (Equiv.swap 0 1) x.2
  ((copy, endpoint), sourceParameter i x)

private lemma slotMap_bijective (i : Fin 3) : Function.Bijective (slotMap i) := by
  fin_cases i <;> decide +kernel

private noncomputable def slotEquiv (i : Fin 3) :
    (Fin 6 × Fin 2) ≃ (Fin 2 × Fin 2) × Fin 3 :=
  Equiv.ofBijective (slotMap i) (slotMap_bijective i)

private def triplePiEquiv (n₁ n₂ n₃ : ℕ+) :
    (∀ p : Fin 3, Fin (parameterDim n₁ n₂ n₃ p)) ≃
      (Fin n₁ × Fin n₂) × Fin n₃ where
  toFun f := ((f 0, f 1), f 2)
  invFun x := fun
    | 0 => x.1.1
    | 1 => x.1.2
    | 2 => x.2
  left_inv f := by funext p; fin_cases p <;> rfl
  right_inv _ := rfl

private def targetTupleEquiv (n₁ n₂ n₃ : ℕ+) :
    (∀ x : (Fin 2 × Fin 2) × Fin 3,
      Fin (parameterDim n₁ n₂ n₃ x.2)) ≃
    ((((Fin n₁ × Fin n₂) × Fin n₃) ×
      ((Fin n₁ × Fin n₂) × Fin n₃)) ×
     (((Fin n₁ × Fin n₂) × Fin n₃) ×
      ((Fin n₁ × Fin n₂) × Fin n₃))) := by
  exact (piProdEquiv (fun _ : Fin 2 × Fin 2 =>
      fun p => Fin (parameterDim n₁ n₂ n₃ p))).symm
    |>.trans (Equiv.piCongrRight (fun _ : Fin 2 × Fin 2 =>
      triplePiEquiv n₁ n₂ n₃))
    |>.trans (piProdEquiv (fun _ : Fin 2 => fun _ : Fin 2 =>
      (Fin n₁ × Fin n₂) × Fin n₃)).symm
    |>.trans (Equiv.piCongrRight (fun _ : Fin 2 =>
      piFinTwoEquiv (fun _ : Fin 2 =>
        (Fin n₁ × Fin n₂) × Fin n₃)))
    |>.trans (piFinTwoEquiv (fun _ : Fin 2 =>
      ((Fin n₁ × Fin n₂) × Fin n₃) ×
      ((Fin n₁ × Fin n₂) × Fin n₃)))

private def tripleDecodeEquiv (n₁ n₂ n₃ : ℕ+) :
    Fin (n₁ * n₂ * n₃ : ℕ+) ≃ (Fin n₁ × Fin n₂) × Fin n₃ :=
  (kronDecodeEquiv (d₁ := n₁ * n₂) (d₂ := n₃)).trans
    ((kronDecodeEquiv (d₁ := n₁) (d₂ := n₂)).prodCongr (Equiv.refl _))

private def targetDecodeEquiv (n₁ n₂ n₃ : ℕ+) :
    let N := n₁ * n₂ * n₃
    Fin ((N * N) * (N * N) : ℕ+) ≃
    ((((Fin n₁ × Fin n₂) × Fin n₃) ×
      ((Fin n₁ × Fin n₂) × Fin n₃)) ×
     (((Fin n₁ × Fin n₂) × Fin n₃) ×
      ((Fin n₁ × Fin n₂) × Fin n₃))) :=
  (kronDecodeEquiv (d₁ := (n₁ * n₂ * n₃) * (n₁ * n₂ * n₃))
      (d₂ := (n₁ * n₂ * n₃) * (n₁ * n₂ * n₃))).trans
    (((kronDecodeEquiv (d₁ := n₁ * n₂ * n₃) (d₂ := n₁ * n₂ * n₃)).trans
        ((tripleDecodeEquiv n₁ n₂ n₃).prodCongr
          (tripleDecodeEquiv n₁ n₂ n₃))).prodCongr
      ((kronDecodeEquiv (d₁ := n₁ * n₂ * n₃) (d₂ := n₁ * n₂ * n₃)).trans
        ((tripleDecodeEquiv n₁ n₂ n₃).prodCongr
          (tripleDecodeEquiv n₁ n₂ n₃))))

private noncomputable def symmSplitEquiv (n₁ n₂ n₃ : ℕ+) (i : Fin 3) :
    Fin (∏ π : Equiv.Perm (Fin 3),
      OM.PolMul.fmt (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) (π.symm i)) ≃
    ∀ π : Equiv.Perm (Fin 3),
      Fin (OM.PolMul.fmt (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) (π.symm i)) :=
  (finCongr (by
    rw [Fintype.card_pi]
    simpa only [Fintype.card_fin] using!
      (map_prod PNat.coeMonoidHom
        (fun π : Equiv.Perm (Fin 3) =>
          OM.PolMul.fmt (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) (π.symm i))
        Finset.univ).symm)).trans
    (Fintype.equivFin (∀ π : Equiv.Perm (Fin 3),
      Fin (OM.PolMul.fmt (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) (π.symm i)))).symm

private noncomputable def symmLegEquiv (n₁ n₂ n₃ : ℕ+) (i : Fin 3) :
    Fin (∏ π : Equiv.Perm (Fin 3),
      OM.PolMul.fmt (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) (π.symm i)) ≃
    let N := n₁ * n₂ * n₃
    Fin ((N * N) * (N * N) : ℕ+) := by
  let oldFmt := OM.PolMul.fmt (n₁ * n₂) (n₂ * n₃) (n₃ * n₁)
  let P := fun b : (Fin 2 × Fin 2) × Fin 3 =>
    Fin (parameterDim n₁ n₂ n₃ b.2)
  exact symmSplitEquiv n₁ n₂ n₃ i
    |>.trans (Equiv.piCongrLeft
      (fun π : Equiv.Perm (Fin 3) => Fin (oldFmt (π.symm i)))
      permSixEquiv).symm
    |>.trans (Equiv.piCongrRight (fun q : Fin 6 => finCongr
      (congrArg PNat.val ((congrFun (edgeDim_eq_fmt n₁ n₂ n₃)
        ((permSix q).symm i)).symm))))
    |>.trans (Equiv.piCongrRight (fun q : Fin 6 =>
      edgeCoordinateEquiv n₁ n₂ n₃ ((permSix q).symm i)))
    |>.trans (piProdEquiv (fun q : Fin 6 => fun t : Fin 2 =>
      Fin (parameterDim n₁ n₂ n₃
        (edgeParameter ((permSix q).symm i) t))))
    |>.trans (Equiv.piCongrLeft P (slotEquiv i))
    |>.trans (targetTupleEquiv n₁ n₂ n₃)
    |>.trans (targetDecodeEquiv n₁ n₂ n₃).symm

private noncomputable def symmSourceSplit (n₁ n₂ n₃ : ℕ+) (i : Fin 3)
    (x : Fin (∏ π : Equiv.Perm (Fin 3),
      OM.PolMul.fmt (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) (π.symm i))) :=
  symmSplitEquiv n₁ n₂ n₃ i x

private lemma symmLegEquiv_spec (n₁ n₂ n₃ : ℕ+) (i : Fin 3)
    (x : Fin (∏ π : Equiv.Perm (Fin 3),
      OM.PolMul.fmt (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) (π.symm i)))
    (q : Fin 6) (t : Fin 2) :
    let j := (permSix q).symm i
    let source := finCongr
      (congrArg PNat.val ((congrFun (edgeDim_eq_fmt n₁ n₂ n₃) j).symm))
      (symmSourceSplit n₁ n₂ n₃ i x (permSix q))
    let target := (targetTupleEquiv n₁ n₂ n₃).symm
      (targetDecodeEquiv n₁ n₂ n₃ (symmLegEquiv n₁ n₂ n₃ i x))
    target (slotMap i (q, t)) =
      edgeCoordinateEquiv n₁ n₂ n₃ j source t := by
  classical
  dsimp only
  simp only [symmLegEquiv, symmSourceSplit, symmSplitEquiv, Equiv.trans_apply,
    Equiv.apply_symm_apply, Equiv.symm_apply_apply]
  exact Equiv.piCongrLeft_apply_apply
    (fun b : (Fin 2 × Fin 2) × Fin 3 =>
      Fin (parameterDim n₁ n₂ n₃ b.2))
    (slotEquiv i) _ (q, t)

private noncomputable def symmPermIndex (n₁ n₂ n₃ : ℕ+)
    (idx : ∀ i : Fin 3, Fin (∏ π : Equiv.Perm (Fin 3),
      OM.PolMul.fmt (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) (π.symm i)))
    (q : Fin 6) : ∀ j : Fin 3,
      Fin (OM.PolMul.fmt (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) j) :=
  Equiv.piCongrLeft
    (fun j => Fin (OM.PolMul.fmt (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) j))
    (permSix q).symm
    (fun i => symmSourceSplit n₁ n₂ n₃ i (idx i) (permSix q))

private noncomputable def symmSourceScalar (n₁ n₂ n₃ : ℕ+)
    (idx : ∀ i : Fin 3, Fin (∏ π : Equiv.Perm (Fin 3),
      OM.PolMul.fmt (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) (π.symm i)))
    (q : Fin 6) (j : Fin 3) (t : Fin 2) :=
  edgeCoordinateEquiv n₁ n₂ n₃ j
    (finCongr (congrArg PNat.val
      ((congrFun (edgeDim_eq_fmt n₁ n₂ n₃) j).symm))
      (Fin.cast (congrArg PNat.val (by
        rw [Equiv.symm_apply_apply]))
        (symmSourceSplit n₁ n₂ n₃ ((permSix q) j)
          (idx ((permSix q) j)) (permSix q)))) t

private lemma sourceScalar_at_permIndex (n₁ n₂ n₃ : ℕ+)
    (idx : ∀ i : Fin 3, Fin (∏ π : Equiv.Perm (Fin 3),
      OM.PolMul.fmt (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) (π.symm i)))
    (q : Fin 6) (j : Fin 3) (t : Fin 2) :
    symmSourceScalar n₁ n₂ n₃ idx q j t =
      edgeCoordinateEquiv n₁ n₂ n₃ j
        (finCongr (congrArg PNat.val
          ((congrFun (edgeDim_eq_fmt n₁ n₂ n₃) j).symm))
          (symmPermIndex n₁ n₂ n₃ idx q j)) t := by
  have hsource :
      Fin.cast (congrArg PNat.val (by rw [Equiv.symm_apply_apply]))
          (symmSourceSplit n₁ n₂ n₃ ((permSix q) j)
            (idx ((permSix q) j)) (permSix q)) =
        symmPermIndex n₁ n₂ n₃ idx q j := by
    apply Fin.ext
    unfold symmPermIndex
    rw [piCongrLeft_val]
    simp only [Equiv.symm_symm, Fin.val_cast]
  unfold symmSourceScalar
  rw [hsource]

private lemma permMatMul_at_split (n₁ n₂ n₃ : ℕ+)
    (idx : ∀ i : Fin 3, Fin (∏ π : Equiv.Perm (Fin 3),
      OM.PolMul.fmt (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) (π.symm i)))
    (q : Fin 6) :
    OM.PolMul.perm (permSix q) (OM.PolMul.matMul (F := F) n₁ n₂ n₃)
      (fun i => symmSourceSplit n₁ n₂ n₃ i (idx i) (permSix q)) =
    if symmSourceScalar n₁ n₂ n₃ idx q 0 1 =
          symmSourceScalar n₁ n₂ n₃ idx q 1 0 ∧
       symmSourceScalar n₁ n₂ n₃ idx q 1 1 =
          symmSourceScalar n₁ n₂ n₃ idx q 2 0 ∧
       symmSourceScalar n₁ n₂ n₃ idx q 2 1 =
          symmSourceScalar n₁ n₂ n₃ idx q 0 0
    then 1 else 0 := by
  simp only [OM.PolMul.perm, KTensor.legReindex, matMul_apply_decode]
  congr 1
  apply propext
  have h₀₀ : symmSourceScalar n₁ n₂ n₃ idx q 0 0 =
      (kronDecodeEquiv (symmPermIndex n₁ n₂ n₃ idx q 0)).1 := by
    rw [sourceScalar_at_permIndex]
    rfl
  have h₀₁ : symmSourceScalar n₁ n₂ n₃ idx q 0 1 =
      (kronDecodeEquiv (symmPermIndex n₁ n₂ n₃ idx q 0)).2 := by
    rw [sourceScalar_at_permIndex]
    rfl
  have h₁₀ : symmSourceScalar n₁ n₂ n₃ idx q 1 0 =
      (kronDecodeEquiv (symmPermIndex n₁ n₂ n₃ idx q 1)).1 := by
    rw [sourceScalar_at_permIndex]
    rfl
  have h₁₁ : symmSourceScalar n₁ n₂ n₃ idx q 1 1 =
      (kronDecodeEquiv (symmPermIndex n₁ n₂ n₃ idx q 1)).2 := by
    rw [sourceScalar_at_permIndex]
    rfl
  have h₂₀ : symmSourceScalar n₁ n₂ n₃ idx q 2 0 =
      (kronDecodeEquiv (symmPermIndex n₁ n₂ n₃ idx q 2)).1 := by
    rw [sourceScalar_at_permIndex]
    rfl
  have h₂₁ : symmSourceScalar n₁ n₂ n₃ idx q 2 1 =
      (kronDecodeEquiv (symmPermIndex n₁ n₂ n₃ idx q 2)).2 := by
    rw [sourceScalar_at_permIndex]
    rfl
  change
    ((kronDecodeEquiv (symmPermIndex n₁ n₂ n₃ idx q 0)).2 =
        (kronDecodeEquiv (symmPermIndex n₁ n₂ n₃ idx q 1)).1 ∧
      (kronDecodeEquiv (symmPermIndex n₁ n₂ n₃ idx q 1)).2 =
          (kronDecodeEquiv (symmPermIndex n₁ n₂ n₃ idx q 2)).1 ∧
      (kronDecodeEquiv (symmPermIndex n₁ n₂ n₃ idx q 2)).2 =
        (kronDecodeEquiv (symmPermIndex n₁ n₂ n₃ idx q 0)).1) ↔ _
  simp only [← h₀₀, ← h₀₁, ← h₁₀, ← h₁₁, ← h₂₀, ← h₂₁]

private noncomputable def symmTargetScalar (n₁ n₂ n₃ : ℕ+)
    (idx : ∀ i : Fin 3, Fin (∏ π : Equiv.Perm (Fin 3),
      OM.PolMul.fmt (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) (π.symm i)))
    (i : Fin 3) (c t : Fin 2) (p : Fin 3) :=
  (targetTupleEquiv n₁ n₂ n₃).symm
    (targetDecodeEquiv n₁ n₂ n₃ (symmLegEquiv n₁ n₂ n₃ i (idx i)))
    ((c, t), p)

private lemma sourceScalar_eq_target (n₁ n₂ n₃ : ℕ+)
    (idx : ∀ i : Fin 3, Fin (∏ π : Equiv.Perm (Fin 3),
      OM.PolMul.fmt (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) (π.symm i)))
    (q : Fin 6) (j : Fin 3) (t : Fin 2) :
    symmTargetScalar n₁ n₂ n₃ idx ((permSix q) j)
        (if q.val < 3 then 0 else 1)
        (if q.val < 3 then t else (Equiv.swap 0 1) t)
        (edgeParameter j t) =
      symmSourceScalar n₁ n₂ n₃ idx q j t := by
  classical
  have h := symmLegEquiv_spec n₁ n₂ n₃ ((permSix q) j)
    (idx ((permSix q) j)) q t
  fin_cases q <;> fin_cases j <;> fin_cases t <;>
    simpa [symmTargetScalar, symmSourceScalar, slotMap, sourceParameter,
      permSix, edgeParameter, nextThree] using! h

private def targetDecodedEndpoint (n₁ n₂ n₃ : ℕ+)
    (z : Fin ((((n₁ * n₂ * n₃) * (n₁ * n₂ * n₃)) *
      ((n₁ * n₂ * n₃) * (n₁ * n₂ * n₃)) : ℕ+) : ℕ))
    (c t : Fin 2) : Fin (n₁ * n₂ * n₃ : ℕ+) :=
  match c, t with
  | 0, 0 => (kronDecodeEquiv (kronDecodeEquiv z).1).1
  | 0, 1 => (kronDecodeEquiv (kronDecodeEquiv z).1).2
  | 1, 0 => (kronDecodeEquiv (kronDecodeEquiv z).2).1
  | 1, 1 => (kronDecodeEquiv (kronDecodeEquiv z).2).2

private lemma targetScalar_decode (n₁ n₂ n₃ : ℕ+)
    (idx : ∀ i : Fin 3, Fin (∏ π : Equiv.Perm (Fin 3),
      OM.PolMul.fmt (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) (π.symm i)))
    (i : Fin 3) (c t : Fin 2) (p : Fin 3) :
    symmTargetScalar n₁ n₂ n₃ idx i c t p =
      (triplePiEquiv n₁ n₂ n₃).symm
        (tripleDecodeEquiv n₁ n₂ n₃
          (targetDecodedEndpoint n₁ n₂ n₃
            (symmLegEquiv n₁ n₂ n₃ i (idx i)) c t)) p := by
  fin_cases c <;> fin_cases t <;> fin_cases p <;> rfl

private lemma targetEndpoint_eq_iff (n₁ n₂ n₃ : ℕ+)
    (idx : ∀ i : Fin 3, Fin (∏ π : Equiv.Perm (Fin 3),
      OM.PolMul.fmt (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) (π.symm i)))
    (i k : Fin 3) (c t u : Fin 2) :
    targetDecodedEndpoint n₁ n₂ n₃
        (symmLegEquiv n₁ n₂ n₃ i (idx i)) c t =
      targetDecodedEndpoint n₁ n₂ n₃
        (symmLegEquiv n₁ n₂ n₃ k (idx k)) c u ↔
    ∀ p : Fin 3, symmTargetScalar n₁ n₂ n₃ idx i c t p =
      symmTargetScalar n₁ n₂ n₃ idx k c u p := by
  constructor
  · intro h p
    rw [targetScalar_decode, targetScalar_decode, h]
  · intro h
    apply (tripleDecodeEquiv n₁ n₂ n₃).injective
    apply (triplePiEquiv n₁ n₂ n₃).symm.injective
    funext p
    simpa only [← targetScalar_decode] using! h p

private def targetCycleCondition (n₁ n₂ n₃ : ℕ+)
    (idx : ∀ i : Fin 3, Fin (∏ π : Equiv.Perm (Fin 3),
      OM.PolMul.fmt (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) (π.symm i)))
    (c : Fin 2) : Prop :=
  (∀ p : Fin 3, symmTargetScalar n₁ n₂ n₃ idx 0 c 1 p =
    symmTargetScalar n₁ n₂ n₃ idx 1 c 0 p) ∧
  (∀ p : Fin 3, symmTargetScalar n₁ n₂ n₃ idx 1 c 1 p =
    symmTargetScalar n₁ n₂ n₃ idx 2 c 0 p) ∧
  (∀ p : Fin 3, symmTargetScalar n₁ n₂ n₃ idx 2 c 1 p =
    symmTargetScalar n₁ n₂ n₃ idx 0 c 0 p)

private def sourceCycleCondition (n₁ n₂ n₃ : ℕ+)
    (idx : ∀ i : Fin 3, Fin (∏ π : Equiv.Perm (Fin 3),
      OM.PolMul.fmt (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) (π.symm i)))
    (q : Fin 6) : Prop :=
  symmSourceScalar n₁ n₂ n₃ idx q 0 1 =
      symmSourceScalar n₁ n₂ n₃ idx q 1 0 ∧
    symmSourceScalar n₁ n₂ n₃ idx q 1 1 =
        symmSourceScalar n₁ n₂ n₃ idx q 2 0 ∧
      symmSourceScalar n₁ n₂ n₃ idx q 2 1 =
        symmSourceScalar n₁ n₂ n₃ idx q 0 0

-- Normalizing all eighteen scalar incidences is elaboration-heavy.
set_option maxHeartbeats 500000 in
private lemma sourceConditions_iff (n₁ n₂ n₃ : ℕ+)
    (idx : ∀ i : Fin 3, Fin (∏ π : Equiv.Perm (Fin 3),
      OM.PolMul.fmt (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) (π.symm i))) :
    sourceCycleCondition n₁ n₂ n₃ idx 0 ∧
      sourceCycleCondition n₁ n₂ n₃ idx 1 ∧
      sourceCycleCondition n₁ n₂ n₃ idx 2 ∧
      sourceCycleCondition n₁ n₂ n₃ idx 3 ∧
      sourceCycleCondition n₁ n₂ n₃ idx 4 ∧
      sourceCycleCondition n₁ n₂ n₃ idx 5 ↔
    targetCycleCondition n₁ n₂ n₃ idx 0 ∧
      targetCycleCondition n₁ n₂ n₃ idx 1 := by
  simp only [sourceCycleCondition, targetCycleCondition,
    Fin.forall_fin_succ, Fin.forall_fin_zero,
    ← sourceScalar_eq_target]
  simp only [permSix, edgeParameter, nextThree, Equiv.swap_apply_def,
    Fin.isValue, reduceIte]
  aesop

private lemma symmProduct_reindex (n₁ n₂ n₃ : ℕ+)
    (idx : ∀ i : Fin 3, Fin (∏ π : Equiv.Perm (Fin 3),
      OM.PolMul.fmt (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) (π.symm i))) :
    (∏ π : Equiv.Perm (Fin 3),
      OM.PolMul.perm π (OM.PolMul.matMul (F := F) n₁ n₂ n₃)
        (fun i => symmSourceSplit n₁ n₂ n₃ i (idx i) π)) =
    ∏ q : Fin 6,
      OM.PolMul.perm (permSix q) (OM.PolMul.matMul (F := F) n₁ n₂ n₃)
        (fun i => symmSourceSplit n₁ n₂ n₃ i (idx i) (permSix q)) := by
  exact (permSixEquiv.prod_comp fun π =>
    OM.PolMul.perm π (OM.PolMul.matMul (F := F) n₁ n₂ n₃)
      (fun i => symmSourceSplit n₁ n₂ n₃ i (idx i) π)).symm

private noncomputable def indicator (P : Prop) : F := by
  classical
  exact if P then 1 else 0

private lemma indicator_eq_if (P : Prop) [Decidable P] :
    indicator (F := F) P = if P then 1 else 0 := by
  classical
  by_cases h : P <;> simp [indicator, h]

private lemma sixIndicators (P₀ P₁ P₂ P₃ P₄ P₅ Q₀ Q₁ : Prop)
    (h : P₀ ∧ P₁ ∧ P₂ ∧ P₃ ∧ P₄ ∧ P₅ ↔ Q₀ ∧ Q₁) :
    indicator (F := F) P₀ * indicator P₁ * indicator P₂ *
      indicator P₃ * indicator P₄ * indicator P₅ =
    indicator Q₀ * indicator Q₁ := by
  classical
  unfold indicator
  by_cases h₀ : P₀ <;> by_cases h₁ : P₁ <;> by_cases h₂ : P₂ <;>
    by_cases h₃ : P₃ <;> by_cases h₄ : P₄ <;> by_cases h₅ : P₅ <;>
    by_cases hq₀ : Q₀ <;> by_cases hq₁ : Q₁ <;> simp_all

-- Expanding the six finite factors requires substantial dependent reduction.
set_option maxHeartbeats 800000 in
private lemma sourceProduct_value (n₁ n₂ n₃ : ℕ+)
    (idx : ∀ i : Fin 3, Fin (∏ π : Equiv.Perm (Fin 3),
      OM.PolMul.fmt (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) (π.symm i))) :
    (∏ π : Equiv.Perm (Fin 3),
      OM.PolMul.perm π (OM.PolMul.matMul (F := F) n₁ n₂ n₃)
        (fun i => symmSourceSplit n₁ n₂ n₃ i (idx i) π)) =
    indicator (F := F) (targetCycleCondition n₁ n₂ n₃ idx 0) *
      indicator (targetCycleCondition n₁ n₂ n₃ idx 1) := by
  classical
  rw [symmProduct_reindex, Fin.prod_univ_six,
    permMatMul_at_split, permMatMul_at_split, permMatMul_at_split,
    permMatMul_at_split, permMatMul_at_split, permMatMul_at_split]
  simp only [← indicator_eq_if]
  change
    indicator (F := F) (sourceCycleCondition n₁ n₂ n₃ idx 0) *
      indicator (sourceCycleCondition n₁ n₂ n₃ idx 1) *
      indicator (sourceCycleCondition n₁ n₂ n₃ idx 2) *
      indicator (sourceCycleCondition n₁ n₂ n₃ idx 3) *
      indicator (sourceCycleCondition n₁ n₂ n₃ idx 4) *
      indicator (sourceCycleCondition n₁ n₂ n₃ idx 5) =
    indicator (targetCycleCondition n₁ n₂ n₃ idx 0) *
      indicator (targetCycleCondition n₁ n₂ n₃ idx 1)
  exact sixIndicators _ _ _ _ _ _ _ _ (sourceConditions_iff n₁ n₂ n₃ idx)

-- Decoding both grouped Kronecker coordinates is kernel-intensive.
set_option maxHeartbeats 800000 in
private lemma targetKron_value (n₁ n₂ n₃ : ℕ+)
    (idx : ∀ i : Fin 3, Fin (∏ π : Equiv.Perm (Fin 3),
      OM.PolMul.fmt (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) (π.symm i))) :
    let N := n₁ * n₂ * n₃
    OM.PolMul.kron (OM.PolMul.matMul (F := F) N N N) (OM.PolMul.matMul N N N)
      (fun
        | 0 => symmLegEquiv n₁ n₂ n₃ 0 (idx 0)
        | 1 => symmLegEquiv n₁ n₂ n₃ 1 (idx 1)
        | 2 => symmLegEquiv n₁ n₂ n₃ 2 (idx 2)) =
    indicator (F := F) (targetCycleCondition n₁ n₂ n₃ idx 0) *
      indicator (targetCycleCondition n₁ n₂ n₃ idx 1) := by
  classical
  dsimp only
  simp only [OM.PolMul.kron, kroneckerTensor, matMul_apply_decode]
  change
    (if
      targetDecodedEndpoint n₁ n₂ n₃ (symmLegEquiv n₁ n₂ n₃ 0 (idx 0)) 0 1 =
          targetDecodedEndpoint n₁ n₂ n₃ (symmLegEquiv n₁ n₂ n₃ 1 (idx 1)) 0 0 ∧
        targetDecodedEndpoint n₁ n₂ n₃ (symmLegEquiv n₁ n₂ n₃ 1 (idx 1)) 0 1 =
            targetDecodedEndpoint n₁ n₂ n₃ (symmLegEquiv n₁ n₂ n₃ 2 (idx 2)) 0 0 ∧
          targetDecodedEndpoint n₁ n₂ n₃ (symmLegEquiv n₁ n₂ n₃ 2 (idx 2)) 0 1 =
            targetDecodedEndpoint n₁ n₂ n₃ (symmLegEquiv n₁ n₂ n₃ 0 (idx 0)) 0 0
      then 1 else 0) *
    (if
      targetDecodedEndpoint n₁ n₂ n₃ (symmLegEquiv n₁ n₂ n₃ 0 (idx 0)) 1 1 =
          targetDecodedEndpoint n₁ n₂ n₃ (symmLegEquiv n₁ n₂ n₃ 1 (idx 1)) 1 0 ∧
        targetDecodedEndpoint n₁ n₂ n₃ (symmLegEquiv n₁ n₂ n₃ 1 (idx 1)) 1 1 =
            targetDecodedEndpoint n₁ n₂ n₃ (symmLegEquiv n₁ n₂ n₃ 2 (idx 2)) 1 0 ∧
          targetDecodedEndpoint n₁ n₂ n₃ (symmLegEquiv n₁ n₂ n₃ 2 (idx 2)) 1 1 =
            targetDecodedEndpoint n₁ n₂ n₃ (symmLegEquiv n₁ n₂ n₃ 0 (idx 0)) 1 0
      then 1 else 0) = _
  simp only [targetEndpoint_eq_iff]
  simp only [← indicator_eq_if]
  rfl

-- Relating the library's packed symmetrization index to `symmSourceSplit`
-- requires reduction through the finite-product cardinality proof.
set_option maxHeartbeats 300000 in
private lemma symmMatMul_value (n₁ n₂ n₃ : ℕ+)
    (idx : ∀ i : Fin 3, Fin (∏ π : Equiv.Perm (Fin 3),
      OM.PolMul.fmt (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) (π.symm i))) :
    OM.PolMul.symm (OM.PolMul.matMul (F := F) n₁ n₂ n₃) idx =
      indicator (targetCycleCondition n₁ n₂ n₃ idx 0) *
        indicator (targetCycleCondition n₁ n₂ n₃ idx 1) := by
  unfold OM.PolMul.symm
  change (∏ π : Equiv.Perm (Fin 3),
    OM.PolMul.perm π (OM.PolMul.matMul (F := F) n₁ n₂ n₃)
      (fun i => symmSourceSplit n₁ n₂ n₃ i (idx i) π)) = _
  exact sourceProduct_value n₁ n₂ n₃ idx

-- The explicit six-permutation coordinate normalization is kernel-intensive.
set_option maxHeartbeats 1200000 in
private lemma iso_symm_matMul (n₁ n₂ n₃ : ℕ+) :
    let N := n₁ * n₂ * n₃
    OM.PolMul.Iso (OM.PolMul.symm (OM.PolMul.matMul (F := F) n₁ n₂ n₃))
      (OM.PolMul.kron (OM.PolMul.matMul N N N) (OM.PolMul.matMul N N N)) := by
  classical
  dsimp only
  let N := n₁ * n₂ * n₃
  let e : ∀ i : Fin 3,
      Fin (∏ π : Equiv.Perm (Fin 3),
        OM.PolMul.fmt (n₁ * n₂) (n₂ * n₃) (n₃ * n₁) (π.symm i)) ≃
      Fin (OM.PolMul.fmt (N * N) (N * N) (N * N) i *
        OM.PolMul.fmt (N * N) (N * N) (N * N) i : ℕ+) := fun
    | 0 => symmLegEquiv n₁ n₂ n₃ 0
    | 1 => symmLegEquiv n₁ n₂ n₃ 1
    | 2 => symmLegEquiv n₁ n₂ n₃ 2
  refine isoOfEquiv
    (OM.PolMul.symm (OM.PolMul.matMul (F := F) n₁ n₂ n₃))
    (OM.PolMul.kron (OM.PolMul.matMul N N N) (OM.PolMul.matMul N N N)) e ?_
  intro idx
  calc
    OM.PolMul.symm (OM.PolMul.matMul (F := F) n₁ n₂ n₃) idx =
        indicator (targetCycleCondition n₁ n₂ n₃ idx 0) *
          indicator (targetCycleCondition n₁ n₂ n₃ idx 1) :=
      symmMatMul_value n₁ n₂ n₃ idx
    _ = OM.PolMul.kron
        (OM.PolMul.matMul (F := F) (n₁ * n₂ * n₃) (n₁ * n₂ * n₃)
          (n₁ * n₂ * n₃))
        (OM.PolMul.matMul (n₁ * n₂ * n₃) (n₁ * n₂ * n₃)
          (n₁ * n₂ * n₃))
        (fun
          | 0 => symmLegEquiv n₁ n₂ n₃ 0 (idx 0)
          | 1 => symmLegEquiv n₁ n₂ n₃ 1 (idx 1)
          | 2 => symmLegEquiv n₁ n₂ n₃ 2 (idx 2)) :=
      (targetKron_value n₁ n₂ n₃ idx).symm
    _ = OM.PolMul.kron (OM.PolMul.matMul N N N) (OM.PolMul.matMul N N N)
        (fun i => e i (idx i)) := by
      dsimp only [e, N]
      congr 1
      funext i
      fin_cases i <;> rfl

/-- The lemma on restriction facts (v).  This follows the
paper's six tensor-leg permutation identities and its explicit coordinate
identification of the symmetrization with a square matrix-multiplication
Kronecker product. -/
theorem proof_RF_5 : OM_S_RF_5 := by
  intro F _ n₁ n₂ n₃
  dsimp only
  exact ⟨iso_rotate_matMul n₁ n₂ n₃,
    iso_rotate_symm_matMul n₁ n₂ n₃,
    iso_swap01_matMul n₁ n₂ n₃,
    iso_swap02_matMul n₁ n₂ n₃,
    iso_swap12_matMul n₁ n₂ n₃,
    iso_symm_matMul n₁ n₂ n₃⟩

end OM.PolMul.RestrictionFacts
