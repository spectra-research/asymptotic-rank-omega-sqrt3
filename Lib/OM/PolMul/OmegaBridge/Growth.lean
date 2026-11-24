/- Adapted from PolMul/OmegaBridge/Growth.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMul.OmegaBridge.Tensors
import Lib.OM.PolMulStatements.DEF_16
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace OM.PolMul.OmegaBridge

open AsymptoticSpectrumDuality
open Semicontinuity
open OM.PolMulDef

universe u

variable (F : Type u) [Field F]

noncomputable def mmClass : TensorClass F 3 :=
  TensorClass.mk ⟨_, matMul (F := F) 2 2 2⟩

noncomputable def pF :=
  tensorStrassenPreorder (F := F) (k := 3) (by norm_num)

private lemma matMul_two_ne_zero : matMul (F := F) 2 2 2 ≠ 0 := by
  intro h
  let idx : ∀ i : Fin 3, Fin (fmt (2 * 2) (2 * 2) (2 * 2) i) := fun i =>
    ⟨0, by fin_cases i <;> norm_num [fmt]⟩
  have hv := congrFun h idx
  norm_num [matMul, finProdFinEquiv_symm_apply, Fin.ext_iff, idx] at hv

lemma one_le_mmClass : pF F |>.rel 1 (mmClass F) := by
  have hclass : mmClass F ≠ 0 := by
    intro h
    have hrank : OM.PolMulDef.tensorRank (matMul (F := F) 2 2 2) = 0 := by
      change Semicontinuity.tensorRank (matMul (F := F) 2 2 2) = 0
      rw [← strassenRank_mk_eq_tensorRank]
      change (pF F).rank (mmClass F) = 0
      rw [h]
      exact (pF F).rank_natCast 0
    exact matMul_two_ne_zero F ((tensorRank_eq_zero_iff _).mp hrank)
  rw [TensorClass.one_def]
  exact unitTensor_one_restricts_of_ne_zero (matMul (F := F) 2 2 2) hclass

lemma one_le_asympRank_mmClass : 1 ≤ (pF F).asympRank (mmClass F) := by
  have h := (pF F).one_le_asympSubrank_le_asympRank (one_le_mmClass F)
  exact h.1.trans h.2

lemma tensorRank_matMul_one : Semicontinuity.tensorRank (matMul (F := F) 1 1 1) = 1 := by
  have hne : Semicontinuity.tensorRank (matMul (F := F) 1 1 1) ≠ 0 := by
    intro h
    have hz := (tensorRank_eq_zero_iff (matMul (F := F) 1 1 1)).mp h
    let idx : ∀ i : Fin 3, Fin (fmt (1 * 1) (1 * 1) (1 * 1) i) := fun i =>
      ⟨0, by fin_cases i <;> norm_num [fmt]⟩
    have hv := congrFun hz idx
    norm_num [matMul, finProdFinEquiv_symm_apply, Fin.ext_iff, idx] at hv
  have hle := tensorRank_matMul_le_cube (F := F) (1 : ℕ+)
  norm_num at hle
  omega

lemma dyadicRank_tendsto :
    Filter.Tendsto
      (fun k : ℕ =>
        (OM.PolMulDef.tensorRank (matMul (F := F) (powTwoPNat k) (powTwoPNat k)
          (powTwoPNat k)) : ℝ) ^ (1 / (k : ℝ)))
      Filter.atTop (nhds ((pF F).asympRank (mmClass F))) := by
  change Filter.Tendsto
    (fun k : ℕ =>
      (Semicontinuity.tensorRank (matMul (F := F) (powTwoPNat k) (powTwoPNat k)
        (powTwoPNat k)) : ℝ) ^ (1 / (k : ℝ)))
    Filter.atTop (nhds ((pF F).asympRank (mmClass F)))
  have hlim := (pF F).asympRank_eq_tendsto (one_le_mmClass F)
  apply hlim.congr'
  filter_upwards [Filter.eventually_ge_atTop 1] with k hk
  rw [tensorRank_matMul_two_pow (F := F) k hk]
  rfl

private lemma tendsto_const_rpow_one_div {C : ℝ} (hC : 0 < C) :
    Filter.Tendsto (fun k : ℕ => C ^ (1 / (k : ℝ)))
      Filter.atTop (nhds 1) := by
  have hinv : Filter.Tendsto (fun k : ℕ => (1 / (k : ℝ)))
      Filter.atTop (nhds 0) := by
    simp only [one_div]
    exact tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hcont : ContinuousAt (fun x : ℝ => C ^ x) 0 :=
    Real.continuousAt_const_rpow hC.ne'
  simpa using! hcont.tendsto.comp hinv

private lemma root_bound_of_admissible {tau C : ℝ}
    (hC : ∀ (n : ℕ), ∀ hn : 1 ≤ n,
      (OM.PolMulDef.tensorRank (matMul (F := F) ⟨n, Nat.zero_lt_one.trans_le hn⟩
        ⟨n, Nat.zero_lt_one.trans_le hn⟩ ⟨n, Nat.zero_lt_one.trans_le hn⟩) : ℝ) ≤
        C * (n : ℝ) ^ tau) :
    (pF F).asympRank (mmClass F) ≤ (2 : ℝ) ^ tau := by
  have hC' : ∀ (n : ℕ), ∀ hn : 1 ≤ n,
      (Semicontinuity.tensorRank (matMul (F := F) ⟨n, Nat.zero_lt_one.trans_le hn⟩
        ⟨n, Nat.zero_lt_one.trans_le hn⟩ ⟨n, Nat.zero_lt_one.trans_le hn⟩) : ℝ) ≤
        C * (n : ℝ) ^ tau := by
    simpa only [OM.PolMulDef.tensorRank] using! hC
  have hCone : 1 ≤ C := by
    have h := hC' 1 (by norm_num)
    simpa [tensorRank_matMul_one F] using! h
  have hCpos : 0 < C := zero_lt_one.trans_le hCone
  have hroot : ∀ k : ℕ, 1 ≤ k →
      ((pF F).rank ((mmClass F) ^ k) : ℝ) ^ (1 / (k : ℝ)) ≤
        C ^ (1 / (k : ℝ)) * (2 : ℝ) ^ tau := by
    intro k hk
    have hpowpos : 1 ≤ 2 ^ k := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero k (by norm_num))
    have hb := hC' (2 ^ k) hpowpos
    change (Semicontinuity.tensorRank (matMul (F := F) (powTwoPNat k) (powTwoPNat k)
      (powTwoPNat k)) : ℝ) ≤ C * (((2 ^ k : ℕ) : ℝ) ^ tau) at hb
    rw [tensorRank_matMul_two_pow (F := F) k hk] at hb
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
    have hmono := Real.rpow_le_rpow (Nat.cast_nonneg _) hb (by positivity : 0 ≤ 1 / (k : ℝ))
    calc
      ((pF F).rank ((mmClass F) ^ k) : ℝ) ^ (1 / (k : ℝ))
          ≤ (C * (((2 ^ k : ℕ) : ℝ) ^ tau)) ^ (1 / (k : ℝ)) := hmono
      _ = C ^ (1 / (k : ℝ)) * (2 : ℝ) ^ tau := by
        rw [Real.mul_rpow hCpos.le (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
        congr 1
        rw [Nat.cast_pow, Nat.cast_ofNat]
        rw [← Real.rpow_natCast (2 : ℝ) k, ← Real.rpow_mul (by positivity),
          ← Real.rpow_mul (by positivity)]
        congr 1
        field_simp
  have hright : Filter.Tendsto
      (fun k : ℕ => C ^ (1 / (k : ℝ)) * (2 : ℝ) ^ tau)
      Filter.atTop (nhds ((2 : ℝ) ^ tau)) := by
    simpa using! (tendsto_const_rpow_one_div hCpos).mul_const ((2 : ℝ) ^ tau)
  exact le_of_tendsto_of_tendsto ((pF F).asympRank_eq_tendsto (one_le_mmClass F))
    hright (Filter.eventually_atTop.2 ⟨1, fun k hk => hroot k hk⟩)

lemma asympRank_le_two_rpow_of_mem_omegaSet {tau : ℝ}
    (htau : tau ∈ {t : ℝ | ∃ C : ℝ, ∀ (n : ℕ), ∀ hn : 1 ≤ n,
      (OM.PolMulDef.tensorRank (matMul (F := F) ⟨n, Nat.zero_lt_one.trans_le hn⟩
        ⟨n, Nat.zero_lt_one.trans_le hn⟩ ⟨n, Nat.zero_lt_one.trans_le hn⟩) : ℝ) ≤
        C * (n : ℝ) ^ t}) :
    (pF F).asympRank (mmClass F) ≤ (2 : ℝ) ^ tau := by
  obtain ⟨C, hC⟩ := htau
  exact root_bound_of_admissible F hC

lemma omegaSet_nonempty :
    {t : ℝ | ∃ C : ℝ, ∀ (n : ℕ), ∀ hn : 1 ≤ n,
      (OM.PolMulDef.tensorRank (matMul (F := F) ⟨n, Nat.zero_lt_one.trans_le hn⟩
        ⟨n, Nat.zero_lt_one.trans_le hn⟩ ⟨n, Nat.zero_lt_one.trans_le hn⟩) : ℝ) ≤
        C * (n : ℝ) ^ t}.Nonempty := by
  refine ⟨3, 1, ?_⟩
  intro n hn
  change (Semicontinuity.tensorRank (matMul (F := F)
    (⟨n, Nat.zero_lt_one.trans_le hn⟩ : ℕ+) (⟨n, Nat.zero_lt_one.trans_le hn⟩ : ℕ+)
    (⟨n, Nat.zero_lt_one.trans_le hn⟩ : ℕ+)) : ℝ) ≤ 1 * (n : ℝ) ^ (3 : ℝ)
  have h := tensorRank_matMul_le_cube (F := F)
    (⟨n, Nat.zero_lt_one.trans_le hn⟩ : ℕ+)
  norm_num
  exact_mod_cast h

lemma omegaSet_bddBelow :
    BddBelow {t : ℝ | ∃ C : ℝ, ∀ (n : ℕ), ∀ hn : 1 ≤ n,
      (OM.PolMulDef.tensorRank (matMul (F := F) ⟨n, Nat.zero_lt_one.trans_le hn⟩
        ⟨n, Nat.zero_lt_one.trans_le hn⟩ ⟨n, Nat.zero_lt_one.trans_le hn⟩) : ℝ) ≤
        C * (n : ℝ) ^ t} := by
  refine ⟨0, ?_⟩
  intro tau htau
  have hrho := asympRank_le_two_rpow_of_mem_omegaSet F htau
  have hone := one_le_asympRank_mmClass F
  have : (1 : ℝ) ≤ (2 : ℝ) ^ tau := hone.trans hrho
  by_contra htau
  have hlt := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2)
    (lt_of_not_ge htau)
  linarith

private lemma le_pow_of_root_le {r B : ℝ} {k : ℕ} (hk : 1 ≤ k)
    (hr : 0 ≤ r) (hroot : r ^ (1 / (k : ℝ)) ≤ B) :
    r ≤ B ^ k := by
  have hkpos : (0 : ℝ) < k := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hmono := Real.rpow_le_rpow (Real.rpow_nonneg hr _) hroot
    (Nat.cast_nonneg k)
  calc
    r = (r ^ (1 / (k : ℝ))) ^ (k : ℝ) := by
      rw [← Real.rpow_mul hr]
      have : (1 / (k : ℝ)) * (k : ℝ) = 1 := by field_simp
      rw [this, Real.rpow_one]
    _ ≤ B ^ (k : ℝ) := hmono
    _ = B ^ k := Real.rpow_natCast B k

private lemma base_pow_eq_dyadic_rpow {B tau : ℝ}
    (hB : B = (2 : ℝ) ^ tau) (k : ℕ) :
    B ^ k = (((2 ^ k : ℕ) : ℝ) ^ tau) := by
  rw [hB, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
    Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast,
    ← Real.rpow_mul (by positivity)]
  congr 1
  ring

private lemma logb_asympRank_add_mem_omegaSet {delta : ℝ} (hdelta : 0 < delta) :
    Real.logb 2 ((pF F).asympRank (mmClass F) + delta) ∈
      {t : ℝ | ∃ C : ℝ, ∀ (n : ℕ), ∀ hn : 1 ≤ n,
        (OM.PolMulDef.tensorRank (matMul (F := F) ⟨n, Nat.zero_lt_one.trans_le hn⟩
          ⟨n, Nat.zero_lt_one.trans_le hn⟩ ⟨n, Nat.zero_lt_one.trans_le hn⟩) : ℝ) ≤
          C * (n : ℝ) ^ t} := by
  let rho := (pF F).asympRank (mmClass F)
  let B := rho + delta
  let tau := Real.logb 2 B
  have hrho : 1 ≤ rho := one_le_asympRank_mmClass F
  have hBgt : rho < B := by dsimp [B]; linarith
  have hBone : 1 ≤ B := hrho.trans hBgt.le
  have hBpos : 0 < B := zero_lt_one.trans_le hBone
  have htau : 0 ≤ tau := by
    dsimp [tau]
    exact (Real.logb_nonneg (by norm_num) hBone)
  have hBpow : B = (2 : ℝ) ^ tau := by
    dsimp [tau]
    exact (Real.rpow_logb (b := 2) (by norm_num) (by norm_num) hBpos).symm
  have hev : ∀ᶠ k : ℕ in Filter.atTop,
      (Semicontinuity.tensorRank (matMul (F := F) (powTwoPNat k) (powTwoPNat k)
        (powTwoPNat k)) : ℝ) ^ (1 / (k : ℝ)) ≤ B := by
    have hopen : Set.Iio B ∈ nhds rho := Iio_mem_nhds hBgt
    filter_upwards [(dyadicRank_tendsto F).eventually hopen] with k hk
    exact hk.le
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 hev
  let C : ℝ := max B (((2 ^ K : ℕ) : ℝ) ^ (3 : ℕ))
  refine ⟨C, ?_⟩
  intro n hn
  let npos : ℕ+ := ⟨n, Nat.zero_lt_one.trans_le hn⟩
  let k := Nat.log 2 n
  change (Semicontinuity.tensorRank (matMul (F := F) npos npos npos) : ℝ) ≤
    C * (n : ℝ) ^ tau
  have hn0 : n ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_one.trans_le hn)
  have hnlt : n < 2 ^ (k + 1) := by
    exact Nat.lt_pow_succ_log_self (by norm_num) n
  by_cases hlarge : K ≤ k + 1
  · have hroot := hK (k + 1) hlarge
    have hdyadic :
        (Semicontinuity.tensorRank (matMul (F := F) (powTwoPNat (k + 1)) (powTwoPNat (k + 1))
          (powTwoPNat (k + 1))) : ℝ) ≤ B ^ (k + 1) := by
      apply le_pow_of_root_le (Nat.succ_le_succ (Nat.zero_le k)) (Nat.cast_nonneg _)
      exact hroot
    have hrankmono := tensorRank_matMul_mono (F := F) (n := npos)
      (m := powTwoPNat (k + 1)) hnlt.le
    have hrank :
        (Semicontinuity.tensorRank (matMul (F := F) npos npos npos) : ℝ) ≤ B ^ (k + 1) := by
      have hmonoR :
          (Semicontinuity.tensorRank (matMul (F := F) npos npos npos) : ℝ) ≤
            (Semicontinuity.tensorRank (matMul (F := F) (powTwoPNat (k + 1))
              (powTwoPNat (k + 1)) (powTwoPNat (k + 1))) : ℝ) := by
        exact_mod_cast hrankmono
      exact hmonoR.trans hdyadic
    have hkpow : B ^ k ≤ (n : ℝ) ^ tau := by
      rw [base_pow_eq_dyadic_rpow hBpow]
      apply Real.rpow_le_rpow (by positivity) _ htau
      exact_mod_cast Nat.pow_log_le_self 2 hn0
    calc
      (Semicontinuity.tensorRank (matMul (F := F) npos npos npos) : ℝ) ≤ B ^ (k + 1) := hrank
      _ = B * B ^ k := by rw [pow_succ, mul_comm]
      _ ≤ B * (n : ℝ) ^ tau := mul_le_mul_of_nonneg_left hkpow hBpos.le
      _ ≤ C * (n : ℝ) ^ tau := by
        gcongr
        exact le_max_left _ _
  · have hsmall : k + 1 ≤ K := Nat.le_of_lt (Nat.lt_of_not_ge hlarge)
    have hnK : n ≤ 2 ^ K := hnlt.le.trans (Nat.pow_le_pow_right (by norm_num) hsmall)
    have hcubic := tensorRank_matMul_le_cube (F := F) npos
    have hnCube : (n : ℝ) ^ (3 : ℕ) ≤ ((2 ^ K : ℕ) : ℝ) ^ (3 : ℕ) := by
      gcongr
    have honepow : (1 : ℝ) ≤ (n : ℝ) ^ tau := by
      rw [← Real.one_rpow tau]
      exact Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hn) htau
    calc
      (Semicontinuity.tensorRank (matMul (F := F) npos npos npos) : ℝ) ≤ (n : ℝ) ^ (3 : ℕ) := by
        exact_mod_cast hcubic
      _ ≤ ((2 ^ K : ℕ) : ℝ) ^ (3 : ℕ) := hnCube
      _ ≤ C := le_max_right _ _
      _ ≤ C * (n : ℝ) ^ tau :=
        le_mul_of_one_le_right (hBpos.le.trans (le_max_left _ _)) honepow

lemma omegaF_le_logb_asympRank :
    omegaF F ≤ Real.logb 2 ((pF F).asympRank (mmClass F)) := by
  let rho := (pF F).asympRank (mmClass F)
  have hrho : 0 < rho := zero_lt_one.trans_le (one_le_asympRank_mmClass F)
  have hseq : Filter.Tendsto (fun n : ℕ => Real.logb 2 (rho + 1 / (n + 1 : ℝ)))
      Filter.atTop (nhds (Real.logb 2 rho)) := by
    have hinv : Filter.Tendsto (fun n : ℕ => (1 / (n + 1 : ℝ)))
        Filter.atTop (nhds 0) := by
      simpa using! (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have harg : Filter.Tendsto (fun n : ℕ => rho + 1 / (n + 1 : ℝ))
        Filter.atTop (nhds rho) := by simpa using! tendsto_const_nhds.add hinv
    exact (Real.continuousAt_logb (b := 2) hrho.ne').tendsto.comp harg
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hseq
  filter_upwards with n
  rw [omegaF]
  apply csInf_le (omegaSet_bddBelow F)
  apply logb_asympRank_add_mem_omegaSet F
  positivity

lemma logb_asympRank_le_omegaF :
    Real.logb 2 ((pF F).asympRank (mmClass F)) ≤ omegaF F := by
  rw [omegaF]
  apply le_csInf (omegaSet_nonempty F)
  intro tau htau
  exact (Real.logb_le_iff_le_rpow (by norm_num)
    (zero_lt_one.trans_le (one_le_asympRank_mmClass F))).2
      (asympRank_le_two_rpow_of_mem_omegaSet F htau)

lemma omegaF_eq_logb_asympRank :
    omegaF F = Real.logb 2 ((pF F).asympRank (mmClass F)) :=
  le_antisymm (omegaF_le_logb_asympRank F) (logb_asympRank_le_omegaF F)

end OM.PolMul.OmegaBridge
