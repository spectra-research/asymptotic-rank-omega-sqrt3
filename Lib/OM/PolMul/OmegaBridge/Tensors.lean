/- Adapted from PolMul/OmegaBridge/Tensors.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMul.SpectralFacts.Tensors

namespace OM.PolMul.OmegaBridge

open AsymptoticSpectrumDuality
open Semicontinuity
open OM.PolMul
open OM.PolMulDef

universe u

variable {F : Type u} [Field F]

private lemma tensorRank_mem_decompositions {d : Fin 3 → ℕ+} (T : T3 F d) :
    tensorRank T ∈ {r : ℕ | ∃ s : Fin r → T3 F d,
      (∀ i, IsSimpleTensor (s i)) ∧ T = ∑ i, s i} := by
  apply Nat.sInf_mem
  exact exists_tensorRank_decomp (F := F) (by norm_num) T

lemma tensorRank_eq_zero_iff {d : Fin 3 → ℕ+} (T : T3 F d) :
    tensorRank T = 0 ↔ T = 0 := by
  constructor
  · intro h
    obtain ⟨s, _, hT⟩ := tensorRank_mem_decompositions T
    calc
      T = ∑ i, s i := hT
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        have hi : i.val < 0 := by simpa [h] using! i.isLt
        omega
  · rintro rfl
    exact tensorRank_zero

lemma tensorRank_unitTensor_le (r : ℕ+) :
    tensorRank (unitTensor F (k := 3) r) ≤ (r : ℕ) := by
  classical
  let s : Fin (r : ℕ) → KTensor F (fun _ : Fin 3 => r) := fun a =>
    simpleTensor (fun _ i => if i = a then 1 else 0)
  change Semicontinuity.tensorRank (unitTensor F (k := 3) r) ≤ (r : ℕ)
  apply Nat.sInf_le
  refine ⟨s, fun a => ⟨_, rfl⟩, ?_⟩
  funext idx
  simp only [unitTensor, Finset.sum_apply, s, simpleTensor]
  by_cases hdiag : ∀ i j : Fin 3, idx i = idx j
  · rw [if_pos hdiag, Finset.sum_eq_single (idx 0)]
    · symm
      apply Finset.prod_eq_one
      intro i _
      simp [hdiag i 0]
    · intro a _ ha
      have hz : (if idx 0 = a then (1 : F) else 0) = 0 := by
        rw [if_neg]
        exact fun h => ha h.symm
      rw [Finset.prod_eq_zero (Finset.mem_univ (0 : Fin 3)) hz]
    · intro h
      exact (h (Finset.mem_univ _)).elim
  · rw [if_neg hdiag]
    symm
    apply Finset.sum_eq_zero
    intro a _
    obtain ⟨i, hi⟩ : ∃ i : Fin 3, idx i ≠ a := by
      by_contra h
      push_neg at h
      apply hdiag
      intro i j
      exact (h i).trans (h j).symm
    rw [Finset.prod_eq_zero (Finset.mem_univ i)]
    simp [hi]

lemma restricts_unitTensor_tensorRank {d : Fin 3 → ℕ+} (T : T3 F d)
    (hr : 0 < tensorRank T) :
    Restricts T (unitTensor F (k := 3) ⟨tensorRank T, hr⟩) := by
  classical
  obtain ⟨s, hs, hT⟩ := tensorRank_mem_decompositions T
  choose v hv using hs
  refine ⟨fun i a q => v q i a, ?_⟩
  intro idx
  rw [congrFun hT idx]
  simp only [Finset.sum_apply, hv, simpleTensor, unitTensor]
  refine Finset.sum_of_injOn (e := fun q : Fin (tensorRank T) =>
      (fun _ : Fin 3 => q)) ?_ ?_ ?_ ?_
  · intro a _ b _ hab
    exact congrFun hab 0
  · intro q _
    exact Finset.mem_univ _
  · intro q _ hq
    have hnondiag : ¬ ∀ i j : Fin 3, q i = q j := by
      intro hdiag
      apply hq
      refine ⟨q 0, (show q 0 ∈ (Finset.univ : Finset (Fin (tensorRank T))) from
        Finset.mem_univ _), ?_⟩
      funext i
      exact (hdiag i 0).symm
    simp [hnondiag]
  · intro q _
    simp

lemma strassenRank_mk_eq_tensorRank {d : Fin 3 → ℕ+} (T : T3 F d) :
    (tensorStrassenPreorder (F := F) (k := 3) (by norm_num)).rank
        (TensorClass.mk ⟨d, T⟩) = tensorRank T := by
  let p := tensorStrassenPreorder (F := F) (k := 3) (by norm_num)
  apply le_antisymm
  · rw [p.rank_le_iff]
    rcases Nat.eq_zero_or_pos (tensorRank T) with hr | hr
    · have hT : T = 0 := (tensorRank_eq_zero_iff T).mp hr
      subst T
      rw [show (TensorClass.mk ⟨d, (0 : T3 F d)⟩ : TensorClass F 3) = 0 by
        rw [TensorClass.zero_def]
        exact TensorClass.mk_eq_of_equiv (zeroT_equiv_zero (F := F) (d := d)).symm]
      have hz : tensorRank (0 : T3 F d) = 0 := tensorRank_zero
      rw [hz]
      exact p.refl 0
    · rw [natCast_eq_unitClass, unitClass, dif_pos hr]
      exact restricts_unitTensor_tensorRank T hr
  · let r := p.rank (TensorClass.mk ⟨d, T⟩)
    have hrel := p.rel_rank (TensorClass.mk ⟨d, T⟩)
    rcases Nat.eq_zero_or_pos r with hr | hr
    · have hres : Restricts T (zeroT : KTensor F (fun _ : Fin 3 => 1)) := by
        change p.rel (TensorClass.mk ⟨d, T⟩) 0
        simpa [r, hr] using! hrel
      have hle := tensorRank_mono_under_Restricts (F := F) (by norm_num) hres
      calc
        tensorRank T ≤ tensorRank (zeroT : KTensor F (fun _ : Fin 3 => 1)) := hle
        _ = 0 := tensorRank_zero
        _ = r := hr.symm
        _ = p.rank (TensorClass.mk ⟨d, T⟩) := rfl
    · have hres : Restricts T (unitTensor F (k := 3) ⟨r, hr⟩) := by
        change p.rel (TensorClass.mk ⟨d, T⟩) (r : TensorClass F 3) at hrel
        rw [natCast_eq_unitClass, unitClass, dif_pos hr] at hrel
        exact hrel
      exact (tensorRank_mono_under_Restricts (F := F) (by norm_num) hres).trans
        (tensorRank_unitTensor_le ⟨r, hr⟩)

private noncomputable def pairClass (i j : Fin 3) (hij : i ≠ j) (r : ℕ+) :
    TensorClass F 3 :=
  TensorClass.mk ⟨_, unitPairTensor (F := F) r i j hij⟩

private lemma pairClass_mul (i j : Fin 3) (hij : i ≠ j) (r s : ℕ+) :
    pairClass (F := F) i j hij r * pairClass i j hij s =
      pairClass i j hij (r * s) := by
  rw [pairClass, pairClass, TensorClass.mk_mul, pairClass]
  exact (TensorClass.mk_eq_of_equiv
    (unitPairTensor_kron_equiv (F := F) i j hij r s)).symm

lemma matMul_class_factor (n₁ n₂ n₃ : ℕ+) :
    (TensorClass.mk ⟨_, matMul (F := F) n₁ n₂ n₃⟩ : TensorClass F 3) =
      pairClass (F := F) 0 2 (by decide +kernel) n₁ *
        pairClass 0 1 (by decide +kernel) n₂ * pairClass 1 2 (by decide +kernel) n₃ := by
  rw [pairClass, pairClass, pairClass, TensorClass.mk_mul, TensorClass.mk_mul]
  exact TensorClass.mk_eq_of_equiv (SpectralFacts.matMul_factor_equiv n₁ n₂ n₃)

lemma matMul_class_mul (n₁ n₂ n₃ m₁ m₂ m₃ : ℕ+) :
    (TensorClass.mk ⟨_, matMul (F := F) n₁ n₂ n₃⟩ : TensorClass F 3) *
        TensorClass.mk ⟨_, matMul (F := F) m₁ m₂ m₃⟩ =
      TensorClass.mk ⟨_, matMul (F := F) (n₁ * m₁) (n₂ * m₂) (n₃ * m₃)⟩ := by
  rw [matMul_class_factor, matMul_class_factor, matMul_class_factor]
  rw [← pairClass_mul (F := F) 0 2 (by decide +kernel) n₁ m₁,
    ← pairClass_mul (F := F) 0 1 (by decide +kernel) n₂ m₂,
    ← pairClass_mul (F := F) 1 2 (by decide +kernel) n₃ m₃]
  ac_rfl

def powTwoPNat (k : ℕ) : ℕ+ :=
  ⟨2 ^ k, pow_pos (by norm_num) k⟩

private lemma powTwoPNat_succ (k : ℕ) :
    powTwoPNat (k + 1) = powTwoPNat k * 2 := by
  apply PNat.coe_injective
  simp [powTwoPNat, pow_succ]

lemma matMul_two_pow_class_succ (k : ℕ) :
    (TensorClass.mk ⟨_, matMul (F := F) (powTwoPNat (k + 1)) (powTwoPNat (k + 1))
      (powTwoPNat (k + 1))⟩ : TensorClass F 3) =
      (TensorClass.mk ⟨_, matMul (F := F) 2 2 2⟩ : TensorClass F 3) ^ (k + 1) := by
  induction k with
  | zero =>
      simp [powTwoPNat]
  | succ k ih =>
      rw [show k + 1 + 1 = (k + 1) + 1 by omega, powTwoPNat_succ, pow_succ,
        ← matMul_class_mul, ih]

lemma tensorRank_matMul_two_pow (k : ℕ) (hk : 1 ≤ k) :
    tensorRank (matMul (F := F) (powTwoPNat k) (powTwoPNat k) (powTwoPNat k)) =
      (tensorStrassenPreorder (F := F) (k := 3) (by norm_num)).rank
        ((TensorClass.mk ⟨_, matMul (F := F) 2 2 2⟩ : TensorClass F 3) ^ k) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.add_comm, show j + 1 = j + 1 by rfl, ← matMul_two_pow_class_succ (F := F) j]
  exact (strassenRank_mk_eq_tensorRank (matMul (F := F)
    (powTwoPNat (j + 1)) (powTwoPNat (j + 1)) (powTwoPNat (j + 1)))).symm

lemma matMul_restricts_of_le {n m : ℕ+} (h : (n : ℕ) ≤ (m : ℕ)) :
    Restricts (matMul (F := F) n n n) (matMul (F := F) m m m) := by
  exact Restricts.trans (SpectralFacts.matMul_factor_equiv n n n).1
    (Restricts.trans
      (Restricts.kron_congr
        (Restricts.kron_congr
          (unitPairTensor_restricts_of_le (F := F) (0 : Fin 3) (2 : Fin 3) (by decide +kernel) h)
          (unitPairTensor_restricts_of_le (F := F) (0 : Fin 3) (1 : Fin 3) (by decide +kernel) h))
        (unitPairTensor_restricts_of_le (F := F) (1 : Fin 3) (2 : Fin 3) (by decide +kernel) h))
      (SpectralFacts.matMul_factor_equiv m m m).2)

lemma tensorRank_matMul_mono {n m : ℕ+} (h : (n : ℕ) ≤ (m : ℕ)) :
    tensorRank (matMul (F := F) n n n) ≤ tensorRank (matMul (F := F) m m m) :=
  tensorRank_mono_under_Restricts (F := F) (by norm_num) (matMul_restricts_of_le h)

lemma tensorRank_matMul_le_cube (n : ℕ+) :
    tensorRank (matMul (F := F) n n n) ≤ (n : ℕ) ^ 3 := by
  rw [← strassenRank_mk_eq_tensorRank, matMul_class_factor]
  let p := tensorStrassenPreorder (F := F) (k := 3) (by norm_num)
  calc
    p.rank (pairClass (F := F) 0 2 (by decide +kernel) n *
        pairClass 0 1 (by decide +kernel) n * pairClass 1 2 (by decide +kernel) n)
        ≤ p.rank (pairClass (F := F) 0 2 (by decide +kernel) n *
          pairClass 0 1 (by decide +kernel) n) * p.rank (pairClass 1 2 (by decide +kernel) n) :=
      p.rank_mul_le _ _
    _ ≤ (p.rank (pairClass (F := F) 0 2 (by decide +kernel) n) *
          p.rank (pairClass 0 1 (by decide +kernel) n)) * p.rank (pairClass 1 2 (by decide +kernel) n) := by
      gcongr
      exact p.rank_mul_le _ _
    _ ≤ (n : ℕ) ^ 3 := by
      have hpair : ∀ (i j : Fin 3) (hij : i ≠ j),
          p.rank (pairClass (F := F) i j hij n) ≤ (n : ℕ) := by
        intro i j hij
        rw [p.rank_le_iff, natCast_eq_unitClass, unitClass, dif_pos n.pos]
        exact SpectralFacts.unitPair_restricts_unitTensor n i j hij
      simpa [pow_succ] using! Nat.mul_le_mul (Nat.mul_le_mul (hpair 0 2 (by decide +kernel))
        (hpair 0 1 (by decide +kernel))) (hpair 1 2 (by decide +kernel))

end OM.PolMul.OmegaBridge
