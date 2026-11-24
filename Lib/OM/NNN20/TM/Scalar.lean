import Lib.OM.NNN20.TM.Sem

/-! # Rational enclosures of `log 2`, `log c` and `2^c`

* `ln2_bounds`: `LN2LO ≤ log 2 ≤ LN2HI` (the series of `log (1 - x)` at `x = 1/2`, 70 terms,
  `Real.abs_log_sub_add_sum_range_le`; the rational comparison is kernel-checked).
* `logI_spec`: `logI c = some (lo, hi)` implies `lo ≤ log c ≤ hi` (`c = 2^k m`, `|1 - m| ≤ 1/2`,
  40 terms of the same series).
* `exp2I_spec`: `(exp2I c).1 ≤ 2^c ≤ (exp2I c).2` (`2^c = 2^⌊c⌋ exp (f log 2)`, the lower
  bound by the partial sum, the upper by `Real.exp_bound'`, 25 terms). -/

namespace OM.NNN20

open Finset
open TM (qfloor_le lt_qfloor_add_one le_qceil qceil_lt_add_one)

/-! ## The series of `log (1 - x)` -/

lemma log1mSeries_go (x : ℚ) : ∀ (k i : ℕ) (s : ℚ),
    log1mSeries.go x k i (x ^ i) s = s + ∑ j ∈ range k, x ^ (i + j + 1) / (i + j + 1 : ℕ)
  | 0, i, s => by simp [log1mSeries.go]
  | k + 1, i, s => by
    rw [log1mSeries.go, ← pow_succ, log1mSeries_go x k (i + 1), sum_range_succ']
    simp only [add_zero, Nat.cast_add, Nat.cast_one]
    rw [add_assoc]
    congr 1
    rw [add_comm]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    rw [show i + 1 + j + 1 = i + (j + 1) + 1 by omega]
    push_cast; ring_nf

lemma log1mSeries_fst (x : ℚ) (n : ℕ) :
    (log1mSeries x n).1 = ∑ j ∈ range n, x ^ (j + 1) / (j + 1 : ℕ) := by
  have := log1mSeries_go x n 0 0
  simp only [pow_zero, zero_add] at this
  exact this

/-- `|S + log (1 - x)| ≤ err` -/
theorem log1mSeries_spec (x : ℚ) (hx : |x| < 1) (n : ℕ) :
    |((log1mSeries x n).1 : ℝ) + Real.log (1 - x)| ≤ (log1mSeries x n).2 := by
  have hxR : |(x : ℝ)| < 1 := by exact_mod_cast hx
  have h := Real.abs_log_sub_add_sum_range_le hxR n
  rw [log1mSeries_fst]
  have e2 : (((log1mSeries x n).2 : ℚ) : ℝ) = |(x : ℝ)| ^ (n + 1) / (1 - |(x : ℝ)|) := by
    simp only [log1mSeries]; push_cast; rfl
  rw [e2]
  push_cast
  convert h using 3

/-! ## `log 2` -/

lemma ln2_rat : LN2LO ≤ (log1mSeries (1 / 2) 70).1 - (log1mSeries (1 / 2) 70).2 ∧
    (log1mSeries (1 / 2) 70).1 + (log1mSeries (1 / 2) 70).2 ≤ LN2HI := by
  decide +kernel

theorem ln2_bounds : (LN2LO : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ LN2HI := by
  have h := log1mSeries_spec (1 / 2) (by norm_num [abs_of_pos]) 70
  have hl : Real.log (1 - ((1 / 2 : ℚ) : ℝ)) = -Real.log 2 := by
    rw [show (1 : ℝ) - ((1 / 2 : ℚ) : ℝ) = 2⁻¹ by push_cast; norm_num, Real.log_inv]
  rw [hl, abs_le] at h
  obtain ⟨r1, r2⟩ := ln2_rat
  have r1' : (LN2LO : ℝ) ≤ ((log1mSeries (1 / 2) 70).1 : ℝ) - ((log1mSeries (1 / 2) 70).2 : ℝ) := by
    exact_mod_cast r1
  have r2' : ((log1mSeries (1 / 2) 70).1 : ℝ) + ((log1mSeries (1 / 2) 70).2 : ℝ) ≤ LN2HI := by
    exact_mod_cast r2
  constructor <;> linarith [h.1, h.2]

lemma LN2LO_pos : (0 : ℝ) < LN2LO := by
  have : (0 : ℚ) < LN2LO := by norm_num [LN2LO]
  exact_mod_cast this

/-! ## `log c` -/

lemma logScale_spec (c : ℚ) : (c : ℝ) = (2 : ℝ) ^ (logScale c).1 * ((logScale c).2 : ℝ) := by
  unfold logScale
  dsimp only
  have h2 : ∀ k : ℤ, (2 : ℝ) ^ k ≠ 0 := fun k => zpow_ne_zero _ (by norm_num)
  split_ifs
  · push_cast
    rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
    field_simp
  · push_cast
    rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
    field_simp
  · push_cast
    field_simp

lemma logBounds_spec (k : ℤ) (m : ℚ) (hm : |1 - m| < 1) :
    ((logBounds k m).1 : ℝ) ≤ k * Real.log 2 + Real.log m ∧
    (k : ℝ) * Real.log 2 + Real.log m ≤ (logBounds k m).2 := by
  have hser := log1mSeries_spec (1 - m) hm 40
  have hlog1 : Real.log (1 - ((1 - m : ℚ) : ℝ)) = Real.log (m : ℝ) := by push_cast; ring_nf
  rw [hlog1] at hser
  obtain ⟨s1, s2⟩ := abs_le.mp hser
  have hl2 := ln2_bounds
  unfold logBounds
  dsimp only
  split_ifs with hk
  · have hk' : (0 : ℝ) ≤ k := by exact_mod_cast hk
    have a1 := mul_le_mul_of_nonneg_left hl2.1 hk'
    have a2 := mul_le_mul_of_nonneg_left hl2.2 hk'
    push_cast
    constructor <;> linarith
  · have hk' : (k : ℝ) ≤ 0 := by exact_mod_cast (not_le.mp hk).le
    have a1 := mul_le_mul_of_nonpos_left hl2.1 hk'
    have a2 := mul_le_mul_of_nonpos_left hl2.2 hk'
    push_cast
    constructor <;> linarith

theorem logI_spec {c : ℚ} {l : ℚ × ℚ} (h : logI c = some l) :
    (l.1 : ℝ) ≤ Real.log c ∧ Real.log c ≤ l.2 := by
  unfold logI at h
  split_ifs at h with hc hx
  cases h
  have hcpos : (0 : ℝ) < c := by exact_mod_cast (not_le.mp hc)
  have hscale := logScale_spec c
  have hmpos : (0 : ℝ) < (logScale c).2 := by
    have h2 : (0 : ℝ) < (2 : ℝ) ^ (logScale c).1 := zpow_pos (by norm_num) _
    rw [hscale] at hcpos
    exact pos_of_mul_pos_right hcpos h2.le
  have hlogc : Real.log c = (logScale c).1 * Real.log 2 + Real.log (logScale c).2 := by
    rw [hscale, Real.log_mul (zpow_ne_zero _ (by norm_num)) hmpos.ne', Real.log_zpow]
  rw [hlogc]
  exact logBounds_spec _ _ (by have := not_lt.mp hx; linarith)

/-! ## `2^c` -/

lemma expSum_go (y : ℚ) : ∀ (k i : ℕ) (s : ℚ),
    expSum.go y k i (y ^ i / (Nat.factorial i : ℚ)) s =
      s + ∑ j ∈ range k, y ^ (i + j + 1) / (Nat.factorial (i + j + 1) : ℚ)
  | 0, i, s => by simp [expSum.go]
  | k + 1, i, s => by
    rw [expSum.go]
    have e : y ^ i / (Nat.factorial i : ℚ) * y / ((i + 1 : ℕ) : ℚ) =
        y ^ (i + 1) / (Nat.factorial (i + 1) : ℚ) := by
      rw [Nat.factorial_succ]; push_cast
      field_simp
      ring
    simp only [e]
    rw [expSum_go y k (i + 1), sum_range_succ']
    simp only [add_zero]
    rw [add_assoc]
    congr 1
    rw [add_comm]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    rw [show i + 1 + j + 1 = i + (j + 1) + 1 by omega]

lemma expSum_eq (y : ℚ) {n : ℕ} (hn : 0 < n) :
    expSum y n = ∑ j ∈ range n, y ^ j / (Nat.factorial j : ℚ) := by
  have := expSum_go y (n - 1) 0 1
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, zero_add] at this
  unfold expSum
  rw [this]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [sum_range_succ']
  simp [add_comm]

lemma expSum_real (y : ℚ) {n : ℕ} (hn : 0 < n) :
    ((expSum y n : ℚ) : ℝ) = ∑ j ∈ range n, (y : ℝ) ^ j / (Nat.factorial j : ℝ) := by
  rw [expSum_eq y hn]; push_cast; rfl

theorem exp2I_spec (c : ℚ) :
    ((exp2I c).1 : ℝ) ≤ (2 : ℝ) ^ (c : ℝ) ∧ (2 : ℝ) ^ (c : ℝ) ≤ (exp2I c).2 := by
  unfold exp2I
  simp only
  set k := qfloor c
  set f : ℚ := c - k
  have hf0 : (0 : ℚ) ≤ f := by have := qfloor_le c; simp only [f]; linarith
  have hf1 : f < 1 := by have := lt_qfloor_add_one c; simp only [f]; linarith
  set g : ℚ := 1208925819614629174706176
  have hg : (0 : ℚ) < g := by norm_num [g]
  set ylo : ℚ := qfloor (f * LN2LO * g) / g
  set yhi : ℚ := qceil (f * LN2HI * g) / g
  have hl2 := ln2_bounds
  have hLlo : (0 : ℚ) ≤ LN2LO := by norm_num [LN2LO]
  have hLhi : LN2HI ≤ 7 / 10 := by norm_num [LN2HI]
  -- ylo ≤ f log 2 ≤ yhi, 0 ≤ ylo, yhi ≤ 1
  have hylo : (ylo : ℝ) ≤ (f : ℝ) * Real.log 2 := by
    have h1 : (ylo : ℚ) ≤ f * LN2LO := by
      simp only [ylo]; rw [div_le_iff₀ hg]; exact qfloor_le _
    have h1' : (ylo : ℝ) ≤ (f : ℝ) * LN2LO := by exact_mod_cast h1
    have : (f : ℝ) * LN2LO ≤ (f : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_left hl2.1 (by exact_mod_cast hf0)
    linarith
  have hyhi : (f : ℝ) * Real.log 2 ≤ yhi := by
    have h1 : f * LN2HI ≤ yhi := by
      simp only [yhi]; rw [le_div_iff₀ hg]; exact le_qceil _
    have h1' : (f : ℝ) * LN2HI ≤ yhi := by exact_mod_cast h1
    have : (f : ℝ) * Real.log 2 ≤ (f : ℝ) * LN2HI :=
      mul_le_mul_of_nonneg_left hl2.2 (by exact_mod_cast hf0)
    linarith
  have hylo0 : (0 : ℚ) ≤ ylo := by
    simp only [ylo]
    apply div_nonneg _ hg.le
    have : (0 : ℚ) ≤ f * LN2LO * g := by positivity
    have hq : (0 : ℤ) ≤ qfloor (f * LN2LO * g) := by
      have := lt_qfloor_add_one (f * LN2LO * g)
      have : (-1 : ℚ) < qfloor (f * LN2LO * g) := by linarith
      exact_mod_cast (show (-1 : ℤ) < qfloor (f * LN2LO * g) by exact_mod_cast this)
    exact_mod_cast hq
  have hyhi1 : yhi ≤ 1 := by
    simp only [yhi]
    rw [div_le_iff₀ hg, one_mul]
    have := qceil_lt_add_one (f * LN2HI * g)
    have hb : f * LN2HI * g ≤ 7 / 10 * g := by
      have : f * LN2HI ≤ 7 / 10 := by nlinarith
      nlinarith
    have : (qceil (f * LN2HI * g) : ℚ) < 7 / 10 * g + 1 := by linarith
    norm_num [g] at this ⊢; linarith
  -- 2^c = 2^k exp(f log 2)
  have h2c : (2 : ℝ) ^ (c : ℝ) = (2 : ℝ) ^ k * Real.exp ((f : ℝ) * Real.log 2) := by
    have : (c : ℝ) = (k : ℝ) + (f : ℝ) := by simp only [f]; push_cast; ring
    rw [this, Real.rpow_add (by norm_num), Real.rpow_intCast, Real.rpow_def_of_pos (by norm_num),
      mul_comm (Real.log 2)]
  rw [h2c]
  have h2k : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) _
  constructor
  · -- lower bound
    have hs := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ ylo by exact_mod_cast hylo0) 25
    have hm := Real.exp_le_exp.mpr hylo
    rw [← expSum_real ylo (by norm_num)] at hs
    push_cast
    exact mul_le_mul_of_nonneg_left (hs.trans hm) h2k.le
  · -- upper bound
    have hb := Real.exp_bound' (show (0 : ℝ) ≤ yhi by
      have : (0 : ℝ) ≤ ylo := by exact_mod_cast hylo0
      linarith) (by exact_mod_cast hyhi1) (show 0 < 25 by norm_num)
    have hm := Real.exp_le_exp.mpr hyhi
    rw [← expSum_real yhi (by norm_num)] at hb
    push_cast
    refine mul_le_mul_of_nonneg_left (hm.trans (hb.trans (le_of_eq ?_))) h2k.le
    norm_num [Nat.factorial]

end OM.NNN20
