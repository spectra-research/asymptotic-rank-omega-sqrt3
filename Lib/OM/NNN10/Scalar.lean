import Lib.OM.NNN10.Numerics
import Lib.OM.NNN8.Scalar
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen

/-! Convexity of the two weighted rate capacities on the entire top face. -/
noncomputable section
namespace OM.NNN10
open NNN8
set_option maxHeartbeats 2000000

def rawRate (k t : ℝ) : ℝ := k * beta - k * (9 / 4 - t) + codeC t
def rate (k t : ℝ) : ℝ := max 0 (rawRate k t)
def weightedRate (k t : ℝ) : ℝ := t * rate k t
def rawWeighted (k t : ℝ) : ℝ := t * rawRate k t
def rateSlope (k t : ℝ) : ℝ := k - 2 + 2 * codeP t
def weightedSlope (k t : ℝ) : ℝ := rawRate k t + t * rateSlope k t

lemma hasDerivAt_codeC (t : ℝ) : HasDerivAt codeC (-2 + 2 * codeP t) t := by
  convert! ((hasDerivAt_const t (13 / 4 : ℝ)).sub
    ((hasDerivAt_id t).const_mul 2)).sub (hasDerivAt_codeG t) using 1 <;>
    simp [codeC] <;> ring

lemma hasDerivAt_codeP (t : ℝ) :
    HasDerivAt codeP (-2 * Real.log 2 * codeP t * (1 - codeP t)) t := by
  have he : HasDerivAt (fun x : ℝ => 9 / 4 - 2 * x) (-2) t := by
    convert! (hasDerivAt_const t (9 / 4 : ℝ)).sub ((hasDerivAt_id t).const_mul 2)
      using 1 <;> ring
  have hp := HasDerivAt.const_rpow (by norm_num : (0 : ℝ) < 2) he
  have hn : 1 + (2 : ℝ) ^ (9 / 4 - 2 * t) ≠ 0 := by positivity
  convert! hp.div ((hasDerivAt_const t (1 : ℝ)).add hp) hn using 1
  dsimp [codeP]
  field_simp
  ring

lemma codeP_bounds {t : ℝ} (ht : t ≤ 1) :
    1 / 2 ≤ codeP t ∧ codeP t ≤ 1 := by
  have hp : 0 < (2 : ℝ) ^ (9 / 4 - 2 * t) := by positivity
  have hp1 : 1 ≤ (2 : ℝ) ^ (9 / 4 - 2 * t) :=
    Real.one_le_rpow (by norm_num) (by linarith)
  constructor
  · apply (le_div_iff₀ (by positivity : 0 < 1 + (2 : ℝ) ^ (9 / 4 - 2 * t))).2
    linarith
  · exact (div_le_one (by positivity)).2 (by linarith)

lemma hasDerivAt_rawRate (k t : ℝ) : HasDerivAt (rawRate k) (rateSlope k t) t := by
  convert! ((hasDerivAt_const t (k * beta)).sub
    (((hasDerivAt_const t (9 / 4 : ℝ)).sub (hasDerivAt_id t)).const_mul k)).add
    (hasDerivAt_codeC t) using 1 <;> simp [rawRate, rateSlope] <;> ring

lemma hasDerivAt_rawWeighted (k t : ℝ) :
    HasDerivAt (rawWeighted k) (weightedSlope k t) t := by
  convert! (hasDerivAt_id t).mul (hasDerivAt_rawRate k t) using 1 <;>
    simp [rawWeighted, weightedSlope] <;> ring

lemma hasDerivAt_weightedSlope (k t : ℝ) :
    HasDerivAt (weightedSlope k)
      (2 * k - 4 + 4 * codeP t - 4 * t * Real.log 2 * codeP t * (1 - codeP t)) t := by
  have hs : HasDerivAt (rateSlope k)
      (-4 * Real.log 2 * codeP t * (1 - codeP t)) t := by
    convert! (hasDerivAt_const t (k - 2)).add ((hasDerivAt_codeP t).const_mul 2)
      using 1 <;> simp [rateSlope] <;> ring
  convert! (hasDerivAt_rawRate k t).add ((hasDerivAt_id t).mul hs) using 1 <;>
    simp [weightedSlope, rateSlope] <;> ring

lemma weighted_second_nonneg {k t : ℝ} (hk : 2 ≤ k) (ht : t ∈ Set.Icc (1 / 4 : ℝ) 1) :
    0 ≤ 2 * k - 4 + 4 * codeP t -
      4 * t * Real.log 2 * codeP t * (1 - codeP t) := by
  obtain ⟨hp, hp1⟩ := codeP_bounds ht.2
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have hl0 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hl1 : Real.log 2 ≤ 1 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)
    linarith
  have hpp0 : 0 ≤ codeP t * (1 - codeP t) := mul_nonneg (by linarith) (by linarith)
  have hpp1 : codeP t * (1 - codeP t) ≤ 1 / 4 := by nlinarith [sq_nonneg (codeP t - 1 / 2)]
  have htl : t * Real.log 2 ≤ 1 := (mul_le_mul_of_nonneg_right ht.2 hl0).trans (by simpa using! hl1)
  have hbound := mul_le_mul htl hpp1 hpp0 (by norm_num : (0 : ℝ) ≤ 1)
  nlinarith

theorem rawWeighted_convex {k : ℝ} (hk : 2 ≤ k) :
    ConvexOn ℝ (Set.Icc (1 / 4 : ℝ) 1) (rawWeighted k) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
    (fun t _ => (hasDerivAt_rawWeighted k t).continuousAt.continuousWithinAt)
    (fun t _ => (hasDerivAt_rawWeighted k t).hasDerivWithinAt)
    (fun t _ => (hasDerivAt_weightedSlope k t).hasDerivWithinAt)
  intro t ht
  exact weighted_second_nonneg hk (interior_subset ht)

theorem weightedRate_convex {k : ℝ} (hk : 2 ≤ k) :
    ConvexOn ℝ (Set.Icc (1 / 4 : ℝ) 1) (weightedRate k) := by
  have he : Set.EqOn (weightedRate k) ((fun _ : ℝ => (0 : ℝ)) ⊔ rawWeighted k)
      (Set.Icc (1 / 4 : ℝ) 1) := by
    intro t ht
    dsimp [weightedRate, rate, rawWeighted]
    rw [mul_max_of_nonneg _ _ (by linarith [ht.1]), mul_zero]
  exact ((convexOn_const (0 : ℝ) (convex_Icc (1 / 4 : ℝ) 1)).sup
    (rawWeighted_convex hk)).congr he.symm

lemma rawRate_monotone {k : ℝ} (hk : 2 ≤ k) :
    MonotoneOn (rawRate k) (Set.Icc (1 / 4 : ℝ) 1) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    (fun t _ => (hasDerivAt_rawRate k t).continuousAt.continuousWithinAt)
    (fun t _ => (hasDerivAt_rawRate k t).differentiableAt.differentiableWithinAt)
  intro t ht
  rw [(hasDerivAt_rawRate k t).deriv]
  have hp := (codeP_bounds (interior_subset ht).2).1
  dsimp [rateSlope]
  linarith

lemma codeC_one_lt : codeC 1 < 1 / 4 := by
  have hp : 1 < (2 : ℝ) ^ (1 / 4 : ℝ) := Real.one_lt_rpow (by norm_num) (by norm_num)
  have hg : 1 < codeG 1 := by
    norm_num [codeG]
    apply (Real.lt_logb_iff_rpow_lt (by norm_num : (1 : ℝ) < 2) (by positivity)).2
    simpa using! (show (2 : ℝ) < 1 + (2 : ℝ) ^ (1 / 4 : ℝ) by linarith)
  dsimp [codeC]
  linarith

theorem rate_mem {k t : ℝ} (hk : k = 2 ∨ k = 3) (ht : t ∈ Set.Icc (1 / 4 : ℝ) 1) :
    0 ≤ rate k t ∧ rate k t < 1 := by
  have hk2 : 2 ≤ k := by rcases hk with rfl | rfl <;> norm_num
  have hm := rawRate_monotone hk2 ht (show (1 : ℝ) ∈ Set.Icc (1 / 4 : ℝ) 1 by norm_num) ht.2
  have hu : rawRate k 1 < 1 := by
    have hb := beta_lt_three_halves
    have hc := codeC_one_lt
    dsimp [rawRate]
    rcases hk with rfl | rfl <;> linarith
  exact ⟨le_max_left _ _, max_lt (by norm_num) (hm.trans_lt hu)⟩

lemma rate_balance_two : rate 2 (3 / 4) = codeC (3 / 4) / 2 := by
  have hc := codeC_balance_pos
  unfold rate rawRate
  rw [beta_eq]
  have he : 2 * (3 / 2 - codeC (3 / 4) / 4) - 2 * (9 / 4 - 3 / 4) + codeC (3 / 4) =
      codeC (3 / 4) / 2 := by ring
  rw [he, max_eq_right (by linarith)]

lemma rate_balance_three : rate 3 (3 / 4) = codeC (3 / 4) / 4 := by
  have hc := codeC_balance_pos
  unfold rate rawRate
  rw [beta_eq]
  have he : 3 * (3 / 2 - codeC (3 / 4) / 4) - 3 * (9 / 4 - 3 / 4) + codeC (3 / 4) =
      codeC (3 / 4) / 4 := by ring
  rw [he, max_eq_right (by linarith)]

end OM.NNN10
