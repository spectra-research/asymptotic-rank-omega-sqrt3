/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Foundations.Tensors.Semicontinuity.SpectralPointExtension
import Foundations.Tensors.Semicontinuity.SpectrumDescend

/-!
# Pair-unit exponents and the concrete tensor adapter

For a three-tensor, `orientedPairUnit F i m` is the rank-`m` pair unit whose
singleton (one-dimensional) mode is `i`.  Our orientation convention is

* `i = 0`: the pair is `(1,2)`;
* `i = 1`: the pair is `(0,2)`;
* `i = 2`: the pair is `(0,1)`.

Thus the orientation is indexed by the omitted/singleton mode, not by an
ordered pair.  The total definition uses `pairUnitTT`, whose zero-rank branch
is harmless; every theorem about pair exponents assumes positive rank.
-/

namespace Foundations.PairUnitExponents

open Filter
open AsymptoticSpectrumDuality
open AsymptoticSpectrumDuality.AsymptoticSpectrum
open Semicontinuity

universe u

/-- The two nonsingleton modes in orientation `i`, written in increasing order. -/
def complementaryPair : Fin 3 → Fin 3 × Fin 3 :=
  ![(1, 2), (0, 2), (0, 1)]

@[simp] theorem complementaryPair_fst_ne_snd (i : Fin 3) :
    (complementaryPair i).1 ≠ (complementaryPair i).2 := by
  fin_cases i <;> decide

@[simp] theorem complementaryPair_fst_lt_snd (i : Fin 3) :
    (complementaryPair i).1 < (complementaryPair i).2 := by
  fin_cases i <;> decide

/-- Bundle a pair unit, with the scalar unit for zero rank or coincident legs. -/
noncomputable def pairUnitTT {F : Type u} [Field F] {k : ℕ} (n : ℕ) (p : Fin k × Fin k) :
    TT F k := by
  classical
  exact if h : p.1 ≠ p.2 ∧ 1 ≤ n then
    ⟨_, unitPairTensor (F := F) ⟨n, h.2⟩ p.1 p.2 h.1⟩
  else ⟨_, unitTensor F (k := k) 1⟩

/-- The oriented pair unit in the concrete tensor-class semiring.

Orientation `i` means that mode `i` is the singleton mode. -/
noncomputable def orientedPairUnit (F : Type u) [Field F] (i : Fin 3) (m : ℕ) :
    TensorClass F 3 :=
  TensorClass.mk (pairUnitTT (F := F) m (complementaryPair i))

/-- On positive ranks, the total `pairUnitTT` definition is the genuine natural-format
pair unit on the two complementary modes. -/
lemma pairUnitTT_complementary_eq {F : Type u} [Field F]
    (i : Fin 3) (m : ℕ) (hm : 0 < m) :
    pairUnitTT (F := F) m (complementaryPair i) =
      ⟨_, unitPairTensor (F := F) ⟨m, hm⟩
        (complementaryPair i).1 (complementaryPair i).2
        (complementaryPair_fst_ne_snd i)⟩ := by
  unfold pairUnitTT
  rw [dif_pos]
  exact ⟨complementaryPair_fst_ne_snd i, by omega⟩

/-- A pair unit of rank `r` is a restriction of the rank-`r` unit tensor.

On the two pair modes the restriction matrices are coordinate identities; on
every singleton mode the unique source coordinate is sent to the all-ones row.
-/
lemma unitPairTensor_restricts_unitTensor {F : Type u} [Field F] {k : ℕ}
    (r : ℕ+) (i j : Fin k) (hij : i ≠ j) :
    Restricts (unitPairTensor (F := F) r i j hij)
      (unitTensor F (k := k) r) := by
  classical
  let A : ∀ ℓ : Fin k,
      Matrix (Fin (naturalPairFormat r i j ℓ)) (Fin r) F :=
    fun ℓ a b => if ℓ = i ∨ ℓ = j then if a.val = b.val then 1 else 0 else 1
  refine ⟨A, ?_⟩
  intro jdx
  unfold unitPairTensor
  by_cases heq : (jdx i).val = (jdx j).val
  · rw [if_pos heq]
    let idx0 : ∀ _ℓ : Fin k, Fin r := fun _ =>
      ⟨(jdx i).val, by
        have hi := (jdx i).isLt
        simpa [naturalPairFormat] using! hi⟩
    rw [Finset.sum_eq_single idx0]
    · have hprod : (∏ ℓ : Fin k, A ℓ (jdx ℓ) (idx0 ℓ)) = 1 := by
        apply Finset.prod_eq_one
        intro ℓ _
        by_cases hℓ : ℓ = i ∨ ℓ = j
        · rcases hℓ with rfl | rfl
          · simp [A, idx0]
          · simp [A, idx0, heq]
        · simp [A, hℓ]
      have hdiag : ∀ a b : Fin k, idx0 a = idx0 b := by
        intro a b
        apply Fin.ext
        rfl
      rw [hprod, one_mul]
      rw [unitTensor, if_pos hdiag]
    · intro idx _ hidx
      by_cases hdiag : ∀ a b : Fin k, idx a = idx b
      · have hi_ne : (jdx i).val ≠ (idx i).val := by
          intro hi
          apply hidx
          funext ℓ
          apply Fin.ext
          calc
            (idx ℓ).val = (idx i).val := congrArg Fin.val (hdiag ℓ i)
            _ = (jdx i).val := hi.symm
            _ = (idx0 ℓ).val := rfl
        have hAi : A i (jdx i) (idx i) = 0 := by
          simp [A, hi_ne]
        rw [Finset.prod_eq_zero (Finset.mem_univ i) hAi, zero_mul]
      · have hunit : unitTensor F (k := k) r idx = 0 := by
          simp [unitTensor, hdiag]
        rw [hunit, mul_zero]
    · intro hnot
      exact (hnot (Finset.mem_univ _)).elim
  · rw [if_neg heq]
    symm
    apply Finset.sum_eq_zero
    intro idx _
    by_cases hdiag : ∀ a b : Fin k, idx a = idx b
    · have hmis :
          (jdx i).val ≠ (idx i).val ∨ (jdx j).val ≠ (idx j).val := by
        by_contra h
        push_neg at h
        apply heq
        calc
          (jdx i).val = (idx i).val := h.1
          _ = (idx j).val := congrArg Fin.val (hdiag i j)
          _ = (jdx j).val := h.2.symm
      rcases hmis with hi_ne | hj_ne
      · have hAi : A i (jdx i) (idx i) = 0 := by
          simp [A, hi_ne]
        rw [Finset.prod_eq_zero (Finset.mem_univ i) hAi, zero_mul]
      · have hAj : A j (jdx j) (idx j) = 0 := by
          simp [A, hj_ne]
        rw [Finset.prod_eq_zero (Finset.mem_univ j) hAj, zero_mul]
    · have hunit : unitTensor F (k := k) r idx = 0 := by
        simp [unitTensor, hdiag]
      rw [hunit, mul_zero]

/-! ## The analytic power lemma -/

/-- A positive, monotone, multiplicative function on the positive natural numbers is
determined by its value at two.  This is the standard floor-and-squeeze argument. -/
theorem monotone_multiplicative_nat_eq_rpow_two
    (f : ℕ → ℝ)
    (hf_one : f 1 = 1)
    (hf_one_le : ∀ n, 0 < n → 1 ≤ f n)
    (hf_mul : ∀ m n, 0 < m → 0 < n → f (m * n) = f m * f n)
    (hf_mono : ∀ m n, 0 < m → 0 < n → m ≤ n → f m ≤ f n)
    (a : ℕ) (ha : 0 < a) :
    f a = f 2 ^ Real.logb 2 a := by
  let L : ℝ := Real.logb 2 a
  let q : ℕ → ℕ := fun k ↦ ⌊(k : ℝ) * L⌋₊
  have hL : 0 ≤ L := by
    exact Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) (by exact_mod_cast ha)
  have hf_pow (n : ℕ) (hn : 0 < n) : ∀ k : ℕ, f (n ^ k) = f n ^ k := by
    intro k
    induction k with
    | zero => simpa using! hf_one
    | succ k ih =>
        rw [pow_succ, hf_mul _ _ (pow_pos hn k) hn, ih, pow_succ]
  have htwo_rpow_L : (2 : ℝ) ^ L = (a : ℝ) := by
    exact Real.rpow_logb (by norm_num) (by norm_num) (by exact_mod_cast ha)
  have hq_le (k : ℕ) : (q k : ℝ) ≤ (k : ℝ) * L := by
    exact Nat.floor_le (mul_nonneg (Nat.cast_nonneg k) hL)
  have hq_lt (k : ℕ) : (k : ℝ) * L < (q k : ℝ) + 1 := by
    exact Nat.lt_floor_add_one ((k : ℝ) * L)
  have hnat_lower (k : ℕ) : 2 ^ q k ≤ a ^ k := by
    have hreal : ((2 ^ q k : ℕ) : ℝ) ≤ ((a ^ k : ℕ) : ℝ) := by
      simp only [Nat.cast_pow, Nat.cast_ofNat]
      calc
        (2 : ℝ) ^ q k = (2 : ℝ) ^ (q k : ℝ) :=
          (Real.rpow_natCast 2 (q k)).symm
        _ ≤ (2 : ℝ) ^ ((k : ℝ) * L) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (hq_le k)
        _ = ((2 : ℝ) ^ L) ^ (k : ℝ) := by
          rw [mul_comm, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        _ = (a : ℝ) ^ (k : ℝ) := by rw [htwo_rpow_L]
        _ = (a : ℝ) ^ k := Real.rpow_natCast a k
    exact_mod_cast hreal
  have hnat_upper (k : ℕ) : a ^ k ≤ 2 ^ (q k + 1) := by
    have hreal : ((a ^ k : ℕ) : ℝ) ≤ ((2 ^ (q k + 1) : ℕ) : ℝ) := by
      simp only [Nat.cast_pow, Nat.cast_ofNat]
      apply le_of_lt
      calc
        (a : ℝ) ^ k = (a : ℝ) ^ (k : ℝ) :=
          (Real.rpow_natCast a k).symm
        _ = ((2 : ℝ) ^ L) ^ (k : ℝ) := by rw [htwo_rpow_L]
        _ = (2 : ℝ) ^ ((k : ℝ) * L) := by
          rw [mul_comm, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        _ < (2 : ℝ) ^ ((q k : ℝ) + 1) :=
          Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (hq_lt k)
        _ = (2 : ℝ) ^ ((q k + 1 : ℕ) : ℝ) := by norm_num
        _ = (2 : ℝ) ^ (q k + 1) := Real.rpow_natCast 2 (q k + 1)
    exact_mod_cast hreal
  have hf_lower (k : ℕ) : f 2 ^ q k ≤ f a ^ k := by
    rw [← hf_pow 2 (by norm_num) (q k), ← hf_pow a ha k]
    exact hf_mono _ _ (pow_pos (by norm_num) _) (pow_pos ha _) (hnat_lower k)
  have hf_upper (k : ℕ) : f a ^ k ≤ f 2 ^ (q k + 1) := by
    rw [← hf_pow a ha k, ← hf_pow 2 (by norm_num) (q k + 1)]
    exact hf_mono _ _ (pow_pos ha _) (pow_pos (by norm_num) _) (hnat_upper k)
  have hX : 1 ≤ f 2 := hf_one_le 2 (by norm_num)
  have hY : 1 ≤ f a := hf_one_le a ha
  have hX0 : 0 ≤ f 2 := zero_le_one.trans hX
  have hY0 : 0 ≤ f a := zero_le_one.trans hY
  have hlower_bound (k : ℕ) (hk : 0 < k) :
      f 2 ^ ((q k : ℝ) / (k : ℝ)) ≤ f a := by
    calc
      f 2 ^ ((q k : ℝ) / (k : ℝ)) =
          (f 2 ^ q k) ^ ((k : ℝ)⁻¹) := by
        rw [div_eq_mul_inv, Real.rpow_mul hX0, Real.rpow_natCast]
      _ ≤ (f a ^ k) ^ ((k : ℝ)⁻¹) :=
        Real.rpow_le_rpow (pow_nonneg hX0 _) (hf_lower k) (by positivity)
      _ = f a := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hY0,
          mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hk.ne'), Real.rpow_one]
  have hupper_bound (k : ℕ) (hk : 0 < k) :
      f a ≤ f 2 ^ (((q k + 1 : ℕ) : ℝ) / (k : ℝ)) := by
    calc
      f a = (f a ^ k) ^ ((k : ℝ)⁻¹) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hY0,
          mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hk.ne'), Real.rpow_one]
      _ ≤ (f 2 ^ (q k + 1)) ^ ((k : ℝ)⁻¹) :=
        Real.rpow_le_rpow (pow_nonneg hY0 _) (hf_upper k) (by positivity)
      _ = f 2 ^ (((q k + 1 : ℕ) : ℝ) / (k : ℝ)) := by
        rw [div_eq_mul_inv, Real.rpow_mul hX0, Real.rpow_natCast]
  have hq_tendsto : Tendsto (fun k : ℕ ↦ (q k : ℝ) / (k : ℝ))
      atTop (nhds L) := by
    have h := (tendsto_nat_floor_mul_div_atTop (R := ℝ) hL).comp
      tendsto_natCast_atTop_atTop
    simpa only [Function.comp_def, q, mul_comm] using! h
  have hinv_tendsto : Tendsto (fun k : ℕ ↦ ((k : ℝ)⁻¹))
      atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hupper_exp_tendsto :
      Tendsto (fun k : ℕ ↦ ((q k + 1 : ℕ) : ℝ) / (k : ℝ))
        atTop (nhds L) := by
    convert! hq_tendsto.add hinv_tendsto using 1 <;> simp
    funext k
    ring
  have hlower_tendsto :
      Tendsto (fun k : ℕ ↦ f 2 ^ ((q k : ℝ) / (k : ℝ)))
        atTop (nhds (f 2 ^ L)) :=
    (Real.continuous_const_rpow (ne_of_gt (zero_lt_one.trans_le hX))).continuousAt.tendsto.comp
      hq_tendsto
  have hupper_tendsto :
      Tendsto (fun k : ℕ ↦ f 2 ^ (((q k + 1 : ℕ) : ℝ) / (k : ℝ)))
        atTop (nhds (f 2 ^ L)) :=
    (Real.continuous_const_rpow (ne_of_gt (zero_lt_one.trans_le hX))).continuousAt.tendsto.comp
      hupper_exp_tendsto
  have hconst_tendsto : Tendsto (fun _ : ℕ ↦ f a) atTop (nhds (f 2 ^ L)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower_tendsto hupper_tendsto
      (eventually_atTop.2 ⟨1, fun k hk ↦ hlower_bound k hk⟩)
      (eventually_atTop.2 ⟨1, fun k hk ↦ hupper_bound k hk⟩)
  simpa [L] using! tendsto_nhds_unique tendsto_const_nhds hconst_tendsto

/-! ## Pair-unit power laws -/

/-- The exponent of the orientation whose singleton mode is `i`. -/
noncomputable def theta {F : Type u} [Field F]
    (φ : AsymptoticSpectrum
      (tensorStrassenPreorder (F := F) (k := 3) (by omega)))
    (i : Fin 3) : ℝ :=
  Real.logb 2
    (eval (tensorStrassenPreorder (F := F) (k := 3) (by omega))
      (orientedPairUnit F i 2) φ)

/-- Every positive integral oriented pair unit obeys the exact power law. -/
theorem eval_orientedPairUnit_eq_rpow {F : Type u} [Field F]
    (φ : AsymptoticSpectrum
      (tensorStrassenPreorder (F := F) (k := 3) (by omega)))
    (i : Fin 3) (m : ℕ) (hm : 0 < m) :
    eval (tensorStrassenPreorder (F := F) (k := 3) (by omega))
        (orientedPairUnit F i m) φ =
      (m : ℝ) ^ theta φ i := by
  let p := tensorStrassenPreorder (F := F) (k := 3) (by omega)
  let ψ : Semicontinuity.SpectralPoint 3 F :=
    ofAbstractSpectralPoint (K := F) (by omega) φ
  let f : ℕ → ℝ := fun n ↦ eval p (orientedPairUnit F i n) φ
  have hf_eq (n : ℕ) (hn : 0 < n) :
      f n = ψ.toFun (unitPairTensor (F := F) ⟨n, hn⟩
        (complementaryPair i).1 (complementaryPair i).2
        (complementaryPair_fst_ne_snd i)) := by
    change eval p (orientedPairUnit F i n) φ = _
    rw [orientedPairUnit, pairUnitTT_complementary_eq i n hn]
    rfl
  have hf_one : f 1 = 1 := by
    rw [hf_eq 1 (by omega)]
    exact ψ.unitPair_one _ _ _
  have hf_one_le : ∀ n, 0 < n → 1 ≤ f n := by
    intro n hn
    rw [hf_eq n hn]
    have hone_n : ((1 : ℕ+) : ℕ) ≤ ((⟨n, hn⟩ : ℕ+) : ℕ) := by
      change 1 ≤ n
      omega
    have hmono := ψ.mono
      (unitPairTensor (F := F) (k := 3) 1
        (complementaryPair i).1 (complementaryPair i).2
        (complementaryPair_fst_ne_snd i))
      (unitPairTensor (F := F) (k := 3) ⟨n, hn⟩
        (complementaryPair i).1 (complementaryPair i).2
        (complementaryPair_fst_ne_snd i))
      (unitPairTensor_restricts_of_le (F := F)
        (complementaryPair i).1 (complementaryPair i).2
        (complementaryPair_fst_ne_snd i) hone_n)
    simpa [ψ.unitPair_one _ _ _] using! hmono
  have hf_mul : ∀ a b, 0 < a → 0 < b → f (a * b) = f a * f b := by
    intro a b ha hb
    rw [hf_eq (a * b) (Nat.mul_pos ha hb), hf_eq a ha, hf_eq b hb]
    have h := ψ.unitPair_mul
      (complementaryPair i).1 (complementaryPair i).2
      (complementaryPair_fst_ne_snd i) ⟨a, ha⟩ ⟨b, hb⟩
    simpa using! h
  have hf_mono : ∀ a b, 0 < a → 0 < b → a ≤ b → f a ≤ f b := by
    intro a b ha hb hab
    rw [hf_eq a ha, hf_eq b hb]
    exact ψ.mono _ _
      (unitPairTensor_restricts_of_le (F := F)
        (complementaryPair i).1 (complementaryPair i).2
        (complementaryPair_fst_ne_snd i) hab)
  have happrox := monotone_multiplicative_nat_eq_rpow_two
    f hf_one hf_one_le hf_mul hf_mono m hm
  have hf2pos : 0 < f 2 := lt_of_lt_of_le zero_lt_one (hf_one_le 2 (by omega))
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast hm
  rw [show eval p (orientedPairUnit F i m) φ = f m from rfl, happrox]
  change f 2 ^ Real.logb 2 m = (m : ℝ) ^ theta φ i
  rw [Real.rpow_def_of_pos hf2pos, Real.rpow_def_of_pos hmpos]
  congr 1
  simp only [Real.logb, theta, f, p]
  ring

/-- Every positive oriented pair unit has spectral value at least one. -/
theorem one_le_eval_orientedPairUnit {F : Type u} [Field F]
    (φ : AsymptoticSpectrum
      (tensorStrassenPreorder (F := F) (k := 3) (by omega)))
    (i : Fin 3) (m : ℕ) (hm : 0 < m) :
    1 ≤ eval (tensorStrassenPreorder (F := F) (k := 3) (by omega))
      (orientedPairUnit F i m) φ := by
  let ψ : Semicontinuity.SpectralPoint 3 F :=
    ofAbstractSpectralPoint (K := F) (by omega) φ
  rw [orientedPairUnit, pairUnitTT_complementary_eq i m hm]
  change 1 ≤ ψ.toFun (unitPairTensor (F := F) ⟨m, hm⟩
    (complementaryPair i).1 (complementaryPair i).2
    (complementaryPair_fst_ne_snd i))
  have hone_m : ((1 : ℕ+) : ℕ) ≤ ((⟨m, hm⟩ : ℕ+) : ℕ) := by
    change 1 ≤ m
    omega
  have hmono := ψ.mono
    (unitPairTensor (F := F) (k := 3) 1
      (complementaryPair i).1 (complementaryPair i).2
      (complementaryPair_fst_ne_snd i))
    (unitPairTensor (F := F) (k := 3) ⟨m, hm⟩
      (complementaryPair i).1 (complementaryPair i).2
      (complementaryPair_fst_ne_snd i))
    (unitPairTensor_restricts_of_le (F := F)
      (complementaryPair i).1 (complementaryPair i).2
      (complementaryPair_fst_ne_snd i) hone_m)
  simpa [ψ.unitPair_one _ _ _] using! hmono

/-- A positive rank-`m` pair unit has spectral value at most `m`, since it
restricts to the rank-`m` unit tensor. -/
theorem eval_orientedPairUnit_le {F : Type u} [Field F]
    (φ : AsymptoticSpectrum
      (tensorStrassenPreorder (F := F) (k := 3) (by omega)))
    (i : Fin 3) (m : ℕ) (hm : 0 < m) :
    eval (tensorStrassenPreorder (F := F) (k := 3) (by omega))
      (orientedPairUnit F i m) φ ≤ (m : ℝ) := by
  let ψ : Semicontinuity.SpectralPoint 3 F :=
    ofAbstractSpectralPoint (K := F) (by omega) φ
  rw [orientedPairUnit, pairUnitTT_complementary_eq i m hm]
  change ψ.toFun (unitPairTensor (F := F) ⟨m, hm⟩
      (complementaryPair i).1 (complementaryPair i).2
      (complementaryPair_fst_ne_snd i)) ≤ (m : ℝ)
  calc
    ψ.toFun (unitPairTensor (F := F) ⟨m, hm⟩
        (complementaryPair i).1 (complementaryPair i).2
        (complementaryPair_fst_ne_snd i))
        ≤ ψ.toFun (unitTensor F (k := 3) ⟨m, hm⟩) :=
      ψ.mono _ _ (unitPairTensor_restricts_unitTensor
        (F := F) ⟨m, hm⟩ _ _ _)
    _ = (m : ℝ) := by simpa using! ψ.normalize (⟨m, hm⟩ : ℕ+)

/-- Each oriented pair exponent lies in the unit interval. -/
theorem theta_mem_Icc {F : Type u} [Field F]
    (φ : AsymptoticSpectrum
      (tensorStrassenPreorder (F := F) (k := 3) (by omega)))
    (i : Fin 3) : theta φ i ∈ Set.Icc (0 : ℝ) 1 := by
  have hone := one_le_eval_orientedPairUnit φ i 2 (by omega)
  have htwo := eval_orientedPairUnit_le φ i 2 (by omega)
  have hpos : 0 < eval (tensorStrassenPreorder (F := F) (k := 3) (by omega))
      (orientedPairUnit F i 2) φ := zero_lt_one.trans_le hone
  constructor
  · exact Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) hone
  · have hlog := Real.logb_le_logb_of_le
      (by norm_num : (1 : ℝ) < 2) hpos htwo
    simpa [theta] using! hlog

end Foundations.PairUnitExponents
