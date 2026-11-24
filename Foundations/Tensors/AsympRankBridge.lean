/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Foundations.Tensors.Semicontinuity.ZariskiSublevel
import Foundations.Tensors.Semicontinuity.TensorStrassenPreorder
import Foundations.AsymptoticSpectrumDuality.RankSubrank

/-!
# The two asymptotic ranks agree (one direction)

Two different `asympRank`s appear in this development and they are **not**
definitionally equal:

* `Semicontinuity.asympRank T = ⨅ₙ R(regroupingMap d n (T^{⊗n}))^{1/n}` for
  `T : KTensor F d` — the one whose sublevel sets are Zariski-closed
  (`Semicontinuity.sublevel_zariski_closed`);
* `(tensorStrassenPreorder hk).asympRank a = sInf {rank_P(aⁿ)^{1/n}}` for a
  class `a : TensorClass F k` — the one produced by the Strassen-duality chain
  (`Foundations.CornerTower4199.asympRank_lt_of_fourPoints_4199`).

This file proves the inequality that the universal bound needs:

`Semicontinuity.asympRank T ≤ (tensorStrassenPreorder hk).asympRank (mk ⟨d,T⟩)`.

The two ingredients are
* `mk_regrouping_pow` — the regrouped `n`-th tensor power represents the `n`-th
  power in the tensor semiring (induction on `n`, with the `n = 1` base handled
  by `powIndexEquiv_one` and the step by
  `regroupingMap_tensorPowerAdd_symm_eq_kron_cast`);
* `tensorRank_le_of_rel_nat` — the Strassen rank of a class dominates the tensor
  rank of any representative.
-/

namespace Foundations.AsympRankBridge

open Semicontinuity AsymptoticSpectrumDuality

universe u

variable {F : Type u} [Field F] {k : ℕ} [NeZero k] {d : Fin k → ℕ+}

/-! ## 1. Format casts and the regrouped power -/

/-- Transporting the format does not change the tensor class. -/
lemma mk_cast {d₁ d₂ : Fin k → ℕ+} (h : d₁ = d₂) (X : KTensor F d₁) :
    TensorClass.mk (⟨d₂, h ▸ X⟩ : TT F k) = TensorClass.mk ⟨d₁, X⟩ := by
  subst h; rfl

private lemma KTensor_cast_apply {d₁ d₂ : Fin k → ℕ+} (h : d₁ = d₂)
    (X : KTensor F d₁) (idx : ∀ i, Fin (d₂ i)) :
    (h ▸ X) idx = X (h.symm ▸ idx) := by
  subst h; rfl

private lemma val_eq_rec_pi_fin {f g : Fin k → ℕ+} (h : f = g)
    (x : ∀ i : Fin k, Fin ((f i : ℕ+) : ℕ)) (i : Fin k) :
    ((h ▸ x : ∀ i, Fin ((g i : ℕ+) : ℕ)) i).val = (x i).val := by
  subst h; rfl

lemma formatPow_one (d : Fin k → ℕ+) : formatPow d 1 = d := by
  funext i; simp [formatPow]

/-- The `n = 1` regrouped power is the tensor itself, up to the format cast. -/
lemma regroupingMap_one (T : KTensor F d) :
    regroupingMap d (1 : ℕ+) (tensorPow (F := F) (V := KTensor F d) (1 : ℕ+) T)
      = (formatPow_one d).symm ▸ T := by
  funext jdx
  change regroupingMap d (1 : ℕ+)
      (PiTensorProduct.tprod F (fun _ : Fin ((1 : ℕ+) : ℕ) => T)) jdx
    = ((formatPow_one d).symm ▸ T) jdx
  rw [regroupingMap_tprod_apply]
  change (∏ jj : Fin 1, T (sliceFun d 1 jdx jj)) = _
  rw [Fin.prod_univ_one]
  rw [KTensor_cast_apply]
  congr 1
  funext i
  apply Fin.ext
  rw [val_eq_rec_pi_fin]
  rw [sliceFun, powIndexEquiv_one]

/-- **The regrouped `n`-th tensor power represents the `n`-th semiring power.** -/
lemma mk_regrouping_pow (T : KTensor F d) (n : ℕ+) :
    TensorClass.mk (⟨formatPow d n,
        regroupingMap d n (tensorPow (F := F) (V := KTensor F d) n T)⟩ : TT F k)
      = (TensorClass.mk (⟨d, T⟩ : TT F k)) ^ (n : ℕ) := by
  induction n using PNat.recOn with
  | one =>
      rw [regroupingMap_one, mk_cast]
      simp
  | succ n ih =>
      have htP := tensorPowerAdd_symm_tensorPow (F := F) (V := KTensor F d) T n
      have hreg_kron := regroupingMap_tensorPowerAdd_symm_eq_kron_cast (F := F) d n 1
        (tensorPow (F := F) (V := KTensor F d) n T)
        (tensorPow (F := F) (V := KTensor F d) 1 T)
      rw [htP] at hreg_kron
      set X := regroupingMap d n (tensorPow (F := F) (V := KTensor F d) n T) with hX
      set Y := regroupingMap d (1 : ℕ+) (tensorPow (F := F) (V := KTensor F d) 1 T) with hY
      have hPNat : (⟨(n : ℕ) + ((1 : ℕ+) : ℕ), Nat.add_pos_left n.pos _⟩ : ℕ+)
          = (n + 1 : ℕ+) := by
        apply PNat.coe_injective
        change (n : ℕ) + ((1 : ℕ+) : ℕ) = ((n + 1 : ℕ+) : ℕ)
        rw [PNat.add_coe]
      have hkey : TensorClass.mk
            (⟨formatPow d ⟨(n : ℕ) + ((1 : ℕ+) : ℕ), Nat.add_pos_left n.pos _⟩,
              regroupingMap d ⟨(n : ℕ) + ((1 : ℕ+) : ℕ), Nat.add_pos_left n.pos _⟩
                (tensorPow (F := F) (V := KTensor F d) (n + 1) T)⟩ : TT F k)
          = TensorClass.mk ⟨_, X ⊠ Y⟩ := by
        rw [← hreg_kron, mk_cast]
      have hkey' : TensorClass.mk
            (⟨formatPow d (n + 1),
              regroupingMap d (n + 1)
                (tensorPow (F := F) (V := KTensor F d) (n + 1) T)⟩ : TT F k)
          = TensorClass.mk ⟨_, X ⊠ Y⟩ := by
        cases hPNat; exact hkey
      rw [hkey', ← TensorClass.mk_mul (⟨formatPow d n, X⟩ : TT F k)
        (⟨formatPow d 1, Y⟩ : TT F k), ih]
      have hone : TensorClass.mk (⟨formatPow d 1, Y⟩ : TT F k)
          = TensorClass.mk (⟨d, T⟩ : TT F k) := by
        rw [hY, regroupingMap_one, mk_cast]
      rw [hone, PNat.add_coe, show ((1 : ℕ+) : ℕ) = 1 from rfl, pow_succ]

/-! ## 2. Tensor rank of a representative is at most the Strassen rank -/

/-- `R(⟨r⟩) ≤ r` for the rank-`r` unit `k`-tensor. -/
lemma tensorRank_unitTensor_le (hk : 2 ≤ k) (r : ℕ+) :
    tensorRank (unitTensor F (k := k) r) ≤ (r : ℕ) := by
  classical
  have hk0 : (0 : ℕ) < k := lt_of_lt_of_le (by norm_num) hk
  refine Nat.sInf_le ⟨fun c : Fin (r : ℕ) =>
    simpleTensor (fun _ : Fin k => fun j : Fin (r : ℕ) => if j = c then (1 : F) else 0),
    fun c => ⟨_, rfl⟩, ?_⟩
  funext jdx
  show unitTensor F (k := k) r jdx = _
  rw [Finset.sum_apply]
  by_cases hall : ∀ a b : Fin k, jdx a = jdx b
  · have hval : unitTensor F (k := k) r jdx = 1 := by
      show (if ∀ a b : Fin k, jdx a = jdx b then (1 : F) else 0) = 1
      rw [if_pos hall]
    rw [hval]
    set i₀ : Fin k := ⟨0, hk0⟩
    rw [Finset.sum_eq_single (jdx i₀)]
    · refine (Finset.prod_eq_one (fun i (_ : i ∈ Finset.univ) => ?_)).symm
      show (if jdx i = jdx i₀ then (1 : F) else 0) = 1
      rw [if_pos (hall i i₀)]
    · intro c _ hc
      refine Finset.prod_eq_zero (Finset.mem_univ i₀) ?_
      show (if jdx i₀ = c then (1 : F) else 0) = 0
      rw [if_neg (fun h => hc h.symm)]
    · intro hnot; exact absurd (Finset.mem_univ _) hnot
  · have hval : unitTensor F (k := k) r jdx = 0 := by
      show (if ∀ a b : Fin k, jdx a = jdx b then (1 : F) else 0) = 0
      rw [if_neg hall]
    rw [hval]
    symm
    push_neg at hall
    obtain ⟨a, b, hab⟩ := hall
    refine Finset.sum_eq_zero (fun c _ => ?_)
    by_cases ha : jdx a = c
    · refine Finset.prod_eq_zero (Finset.mem_univ b) ?_
      show (if jdx b = c then (1 : F) else 0) = 0
      rw [if_neg (fun h => hab (by rw [ha, h]))]
    · refine Finset.prod_eq_zero (Finset.mem_univ a) ?_
      show (if jdx a = c then (1 : F) else 0) = 0
      rw [if_neg ha]

/-- If a class restricts into the natural number `m`, then any representative has
tensor rank at most `m`. -/
lemma tensorRank_le_of_rel_nat (hk : 2 ≤ k) {d' : Fin k → ℕ+} (S : KTensor F d') (m : ℕ)
    (h : (tensorStrassenPreorder (F := F) hk).rel (TensorClass.mk ⟨d', S⟩) (m : TensorClass F k)) :
    tensorRank S ≤ m := by
  have hk1 : 1 ≤ k := le_trans (by norm_num) hk
  rw [natCast_eq_unitClass] at h
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    rw [unitClass, dif_neg (by norm_num)] at h
    have hres : Restricts S (zeroT : KTensor F (fun _ => (1 : ℕ+))) := h
    have hmono := tensorRank_mono_under_Restricts (F := F) hk1 hres
    have hz : tensorRank (F := F) (d := fun _ : Fin k => (1 : ℕ+))
        (zeroT : KTensor F (fun _ => (1 : ℕ+))) = 0 := by
      have hzz : (zeroT : KTensor F (fun _ : Fin k => (1 : ℕ+)))
          = (0 : KTensor F (fun _ : Fin k => (1 : ℕ+))) := rfl
      rw [hzz, tensorRank_zero]
    omega
  · rw [unitClass, dif_pos hm] at h
    have hres : Restricts S (unitTensor F (k := k) ⟨m, hm⟩) := h
    exact le_trans (tensorRank_mono_under_Restricts (F := F) hk1 hres)
      (tensorRank_unitTensor_le (F := F) hk ⟨m, hm⟩)

/-! ## 3. The inequality -/

/-- **`R̃(T) ≤ asympRank_P (mk T)`.** -/
theorem asympRank_le_strassen (hk : 2 ≤ k) (T : KTensor F d) :
    asympRank T ≤ (tensorStrassenPreorder (F := F) hk).asympRank
      (TensorClass.mk (⟨d, T⟩ : TT F k)) := by
  classical
  have hk1 : 1 ≤ k := le_trans (by norm_num) hk
  -- Per-level comparison.
  have hlevel : ∀ n : ℕ+, tensorRank (regroupingMap d n
      (tensorPow (F := F) (V := KTensor F d) n T))
      ≤ (tensorStrassenPreorder (F := F) hk).rank
          ((TensorClass.mk (⟨d, T⟩ : TT F k)) ^ (n : ℕ)) := by
    intro n
    refine tensorRank_le_of_rel_nat (F := F) hk _ _ ?_
    rw [mk_regrouping_pow T n]
    exact ((tensorStrassenPreorder (F := F) hk).rank_le_iff _ _).mp le_rfl
  -- `asympRank T = ⨅ n, (R(regroupingMap ..))^{1/n}`.
  have hasymp : asympRank T = ⨅ n : ℕ+,
      ((tensorRank (regroupingMap d n
        (tensorPow (F := F) (V := KTensor F d) n T)) : ℕ) : ℝ) ^
          ((1 : ℝ) / ((n : ℕ+) : ℕ)) := by
    simp only [asympRank, dif_pos hk1, AdmissibleFunctional.regularize]
    rfl
  have hbdd : BddBelow (Set.range (fun m : ℕ+ =>
      ((tensorRank (regroupingMap d m
        (tensorPow (F := F) (V := KTensor F d) m T)) : ℕ) : ℝ) ^
          ((1 : ℝ) / ((m : ℕ+) : ℕ)))) := by
    refine ⟨0, ?_⟩
    rintro y ⟨m, rfl⟩
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  rw [hasymp]
  refine le_csInf ((tensorStrassenPreorder (F := F) hk).asympRankSet_nonempty _) ?_
  rintro x ⟨n, hn, rfl⟩
  have hnpos : 0 < n := hn
  refine le_trans (ciInf_le hbdd (⟨n, hnpos⟩ : ℕ+)) ?_
  have hmono : ((tensorRank (regroupingMap d (⟨n, hnpos⟩ : ℕ+)
      (tensorPow (F := F) (V := KTensor F d) (⟨n, hnpos⟩ : ℕ+) T)) : ℕ) : ℝ)
      ≤ (((tensorStrassenPreorder (F := F) hk).rank
          ((TensorClass.mk (⟨d, T⟩ : TT F k)) ^ n) : ℕ) : ℝ) := by
    exact_mod_cast hlevel (⟨n, hnpos⟩ : ℕ+)
  have h1n : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  have hfin := Real.rpow_le_rpow (Nat.cast_nonneg _) hmono h1n
  simpa using! hfin

end Foundations.AsympRankBridge
