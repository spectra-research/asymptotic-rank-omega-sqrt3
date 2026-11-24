import Lib.OM.PolMulRect.Defs
import Lib.OM.PolMul.OmegaBridge.Tensors
import Foundations.Tensors.Semicontinuity.ZariskiSublevel

/-! # Finite ranks and growth of rectangular matrix multiplication -/

namespace OM.PolMulRect

open Semicontinuity AsymptoticSpectrumDuality
open PolMul (matMul)
open PolMul.OmegaBridge (matMul_class_mul strassenRank_mk_eq_tensorRank)

universe u
variable {F : Type u} [Field F]

/-- Cropping the three matrix indices can only decrease tensor rank. -/
theorem tensorRank_matMul_mono {A B C A' B' C' : ℕ+}
    (hA : A ≤ A') (hB : B ≤ B') (hC : C ≤ C') :
    tensorRank (matMul (F := F) A B C) ≤ tensorRank (matMul (F := F) A' B' C') := by
  apply tensorRank_mono_under_Restricts (by norm_num)
  exact (PolMul.SpectralFacts.matMul_factor_equiv A B C).1.trans
    (((Restricts.kron_congr
      (Restricts.kron_congr (unitPairTensor_restricts_of_le 0 2 (by decide +kernel) hA)
        (unitPairTensor_restricts_of_le 0 1 (by decide +kernel) hB))
      (unitPairTensor_restricts_of_le 1 2 (by decide +kernel) hC))).trans
        (PolMul.SpectralFacts.matMul_factor_equiv A' B' C').2)

/-- The three pair-unit factors give the naive algorithm with `A * B * C` products. -/
theorem tensorRank_matMul_le_mul (A B C : ℕ+) :
    tensorRank (matMul (F := F) A B C) ≤ (A : ℕ) * B * C := by
  let p := tensorStrassenPreorder (F := F) (k := 3) (by norm_num)
  have pair (r : ℕ+) (i j : Fin 3) (hij : i ≠ j) :
      p.rank (TensorClass.mk ⟨_, unitPairTensor (F := F) r i j hij⟩) ≤ (r : ℕ) := by
    rw [p.rank_le_iff, natCast_eq_unitClass, unitClass]
    simp only [r.pos, ↓reduceDIte]
    exact PolMul.SpectralFacts.unitPair_restricts_unitTensor r i j hij
  rw [← strassenRank_mk_eq_tensorRank]
  change p.rank (TensorClass.mk ⟨_, PolMulDef.matMul (F := F) A B C⟩) ≤ _
  rw [PolMul.OmegaBridge.matMul_class_factor]
  exact (p.rank_mul_le _ _).trans (Nat.mul_le_mul
    ((p.rank_mul_le _ _).trans (Nat.mul_le_mul (pair A 0 2 (by decide +kernel))
      (pair B 0 1 (by decide +kernel)))) (pair C 1 2 (by decide +kernel)))

/-- Fixing the third matrix index exhibits an identity minor of the first flattening. -/
theorem mul_le_flatRank_matMul (A B C : ℕ+) :
    (A : ℕ) * B ≤ flatRank (matMul (F := F) A B C) {0} := by
  classical
  let d := PolMul.fmt (A * B) (B * C) (C * A)
  let cut : Finset (Fin 3) := {0}
  let k : Fin (C : ℕ) := ⟨0, C.pos⟩
  let indices (p : Fin (A : ℕ) × Fin (B : ℕ)) : ∀ i : Fin 3, Fin (d i) :=
    Fin.cases (finProdFinEquiv p) (Fin.cases (finProdFinEquiv (p.2, k))
      (Fin.cases (finProdFinEquiv (k, p.1)) (fun i => i.elim0)))
  let row (p : Fin (A : ℕ) × Fin (B : ℕ)) (i : {i // i ∈ cut}) := indices p i.val
  let col (p : Fin (A : ℕ) × Fin (B : ℕ)) (i : {i // i ∉ cut}) := indices p i.val
  have minor : (flattenMatrix (matMul (F := F) A B C) cut).submatrix row col = 1 := by
    ext p q
    rw [Matrix.submatrix_apply, Matrix.one_apply]
    change (if (finProdFinEquiv.symm (finProdFinEquiv p)).2 =
        (finProdFinEquiv.symm (finProdFinEquiv (q.2, k))).1 ∧
        (finProdFinEquiv.symm (finProdFinEquiv (q.2, k))).2 =
          (finProdFinEquiv.symm (finProdFinEquiv (k, q.1))).1 ∧
        (finProdFinEquiv.symm (finProdFinEquiv (k, q.1))).2 =
          (finProdFinEquiv.symm (finProdFinEquiv p)).1 then (1 : F) else 0) = _
    simp only [Equiv.symm_apply_apply, true_and]
    simp only [Prod.ext_iff, eq_comm (a := q.1) (b := p.1), and_comm]
  have h := Matrix.rank_submatrix_le (flattenMatrix (matMul (F := F) A B C) cut) row col
  rw [minor, Matrix.rank_one, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at h
  exact h

/-- The first flattening gives a lower bound on ordinary rank. -/
theorem mul_le_tensorRank_matMul (A B C : ℕ+) :
    (A : ℕ) * B ≤ tensorRank (matMul (F := F) A B C) :=
  (mul_le_flatRank_matMul A B C).trans (flatRank_le_tensorRank (by norm_num) _ _)

/-- Rounding a positive power of a positive integer costs at most a factor of two. -/
lemma ceil_rpow_le_two_mul {n : ℕ} (hn : 1 ≤ n) {a : ℝ} (ha : 0 ≤ a) :
    (⌈(n : ℝ) ^ a⌉₊ : ℝ) ≤ 2 * (n : ℝ) ^ a := by
  linarith [Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg n) a),
    Real.one_le_rpow (Nat.one_le_cast.mpr hn) ha]

/-- A uniform power comparison on positive integers compares the exponents. -/
lemma exponent_le_of_bound {s t K : ℝ}
    (h : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ^ s ≤ K * (n : ℝ) ^ t) : s ≤ t := by
  by_contra! hts
  have hK : 1 ≤ K := by simpa using h 1 le_rfl
  obtain ⟨n, hn⟩ := exists_nat_gt (max 1 (K ^ (s - t)⁻¹))
  have hn1 : (1 : ℝ) < n := (le_max_left _ _).trans_lt hn
  have hlarge : K < (n : ℝ) ^ (s - t) :=
    (Real.rpow_inv_lt_iff_of_pos (zero_le_one.trans hK) (Nat.cast_nonneg n)
      (sub_pos.mpr hts)).mp ((le_max_right _ _).trans_lt hn)
  have hn0 := zero_lt_one.trans hn1
  have hstrict := mul_lt_mul_of_pos_right hlarge (Real.rpow_pos_of_pos hn0 t)
  rw [← Real.rpow_add hn0, sub_add_cancel] at hstrict
  exact (h n (Nat.one_le_cast.mp hn1.le)).not_gt hstrict

/-- The naive rank bound gives a uniform growth constant of eight. -/
theorem rectAdmissible_nonempty (F : Type u) [Field F] {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    {τ | RectAdmissible F a b c τ}.Nonempty := by
  refine ⟨a + b + c, 8, fun n hn => ?_⟩
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  have h := tensorRank_matMul_le_mul (F := F) (ceilSide n hn a) (ceilSide n hn b) (ceilSide n hn c)
  calc
    _ ≤ (⌈(n : ℝ) ^ a⌉₊ : ℝ) * ⌈(n : ℝ) ^ b⌉₊ * ⌈(n : ℝ) ^ c⌉₊ := by exact_mod_cast h
    _ ≤ (2 * (n : ℝ) ^ a) * (2 * (n : ℝ) ^ b) * (2 * (n : ℝ) ^ c) :=
      mul_le_mul (mul_le_mul (ceil_rpow_le_two_mul hn ha) (ceil_rpow_le_two_mul hn hb)
        (Nat.cast_nonneg _) (by positivity)) (ceil_rpow_le_two_mul hn hc)
        (Nat.cast_nonneg _) (by positivity)
    _ = 8 * (n : ℝ) ^ (a + b + c) := by rw [Real.rpow_add hn0, Real.rpow_add hn0]; ring

/-- Every matrix multiplication tensor of positive sizes has rank at least one. -/
theorem rectAdmissible_bddBelow (F : Type u) [Field F] (a b c : ℝ) :
    BddBelow {τ | RectAdmissible F a b c τ} := by
  refine ⟨0, fun τ ⟨K, hK⟩ => exponent_le_of_bound (K := K) (fun n hn => ?_)⟩
  rw [Real.rpow_zero]
  have hab := mul_le_tensorRank_matMul (F := F) (ceilSide n hn a) (ceilSide n hn b) (ceilSide n hn c)
  have hpos := Nat.mul_pos (ceilSide n hn a).pos (ceilSide n hn b).pos
  exact (show (1 : ℝ) ≤ _ from by exact_mod_cast hpos.trans_le hab).trans (hK n hn)

/-- The first flattening grows at least as `n ^ (a + b)`, including on the boundary. -/
theorem add_le_omegaRect (F : Type u) [Field F] {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    a + b ≤ PolMul.omegaRect F a b c := by
  change a + b ≤ sInf {τ | RectAdmissible F a b c τ}
  apply le_csInf (rectAdmissible_nonempty F ha hb hc)
  rintro τ ⟨K, hK⟩
  apply exponent_le_of_bound (K := K)
  intro n hn
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [Real.rpow_add hn0]
  calc
    _ ≤ (⌈(n : ℝ) ^ a⌉₊ : ℝ) * ⌈(n : ℝ) ^ b⌉₊ :=
      mul_le_mul (Nat.le_ceil _) (Nat.le_ceil _) (by positivity) (Nat.cast_nonneg _)
    _ ≤ _ := by exact_mod_cast mul_le_tensorRank_matMul (F := F)
                  (ceilSide n hn a) (ceilSide n hn b) (ceilSide n hn c)
    _ ≤ _ := hK n hn

/-- The tensor power of a fixed block raises each matrix dimension to that power. -/
theorem matMul_class_pow (A B C : ℕ+) (n : ℕ) :
    (TensorClass.mk ⟨_, matMul (F := F) A B C⟩ : TensorClass F 3) ^ n =
      TensorClass.mk ⟨_, matMul (F := F) (A ^ n) (B ^ n) (C ^ n)⟩ := by
  induction n with
  | zero =>
    change (1 : TensorClass F 3) = TensorClass.mk ⟨_, matMul (F := F) 1 1 1⟩
    rw [TensorClass.one_def]
    apply TensorClass.mk_eq_of_equiv
    apply PolMul.SpectralFacts.restrictsEquiv_of_index_equiv
      (fun i => finCongr (by fin_cases i <;> rfl))
    intro idx
    have uniq (x y : Fin 1) : x = y := Subsingleton.elim _ _
    simp only [matMul, unitTensor]
    exact (ite_eq_left (fun i j => uniq (idx i) (idx j))).trans
      (ite_eq_left ⟨uniq _ _, uniq _ _, uniq _ _⟩).symm
  | succ t ih =>
    simp only [pow_succ, ih]
    exact matMul_class_mul _ _ _ _ _ _

end OM.PolMulRect
