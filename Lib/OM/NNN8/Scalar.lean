import Lib.OM.NNN8.Numerics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Uniform optimisation over the full asymmetric interval, Route 1 (12)–(14). -/
noncomputable section
namespace OM.NNN8
set_option maxHeartbeats 2000000

def codeP (t : ℝ) : ℝ := (2 : ℝ) ^ (9 / 4 - 2 * t) / (1 + (2 : ℝ) ^ (9 / 4 - 2 * t))
def codeRate (t : ℝ) : ℝ := 1 - codeG t / (1 + t)

lemma codeG_pos (t : ℝ) : 0 < codeG t := by
  apply (Real.logb_pos_iff (by norm_num : (1 : ℝ) < 2)
    (by positivity : 0 < 1 + (2 : ℝ) ^ (9 / 4 - 2 * t))).2
  have h := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (9 / 4 - 2 * t)
  linarith

lemma codeG_le_endpoint {t : ℝ} (ht : 3 / 4 ≤ t) : codeG t ≤ codeG (3 / 4) := by
  apply (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) (by positivity) (by positivity)).2
  apply add_le_add le_rfl
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  linarith

lemma codeP_lower {t : ℝ} (ht : t ≤ 1) : 19 / 35 < codeP t := by
  have hu := fourth_root_lower.trans_le
    (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (show (1 / 4 : ℝ) ≤ 9 / 4 - 2 * t by linarith))
  unfold codeP
  apply (lt_div_iff₀ (by positivity : 0 < 1 + (2 : ℝ) ^ (9 / 4 - 2 * t))).2
  linarith

lemma codeRate_mem {t : ℝ} (ht : t ∈ Set.Icc (3 / 4 : ℝ) 1) :
    0 < codeRate t ∧ codeRate t < 1 := by
  have hg := (codeG_le_endpoint ht.1).trans_lt codeG_three_quarters_lt
  have ht0 : 0 < 1 + t := by linarith [ht.1]
  have hdiv : codeG t / (1 + t) < 1 := (div_lt_one ht0).2 (by linarith [ht.1])
  have hpos := div_pos (codeG_pos t) ht0
  dsimp [codeRate]
  constructor <;> linarith

lemma hasDerivAt_codeG (t : ℝ) : HasDerivAt codeG (-2 * codeP t) t := by
  have he : HasDerivAt (fun x : ℝ => 9 / 4 - 2 * x) (-2) t := by
    convert! (hasDerivAt_const t (9 / 4 : ℝ)).sub ((hasDerivAt_id t).const_mul 2) using 1 <;> ring
  have hp := HasDerivAt.const_rpow (by norm_num : (0 : ℝ) < 2) he
  have hl := ((hasDerivAt_const t (1 : ℝ)).add hp).log (by dsimp; positivity)
  have hn : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  convert! hl.div_const (Real.log 2) using 1
  dsimp [codeP]
  field_simp
  ring

lemma hasDerivAt_codeExponent {t : ℝ} (ht : 3 / 4 ≤ t) :
    HasDerivAt codeExponent
      ((codeG t - 2 * t * (1 + t) * codeP t) / (1 + t) ^ (2 : ℕ)) t := by
  have hn : 1 + t ≠ 0 := by linarith
  have hq := (hasDerivAt_id t).div ((hasDerivAt_const t (1 : ℝ)).add (hasDerivAt_id t)) hn
  convert! (hasDerivAt_const t (9 / 4 : ℝ)).add (hq.mul (hasDerivAt_codeG t)) using 1
  dsimp
  field_simp
  ring

lemma codeExponent_deriv_neg {t : ℝ} (ht : t ∈ Set.Icc (3 / 4 : ℝ) 1) :
    deriv codeExponent t < 0 := by
  rw [(hasDerivAt_codeExponent ht.1).deriv]
  apply div_neg_of_neg_of_pos _ (sq_pos_of_pos (by linarith [ht.1]))
  have hg := (codeG_le_endpoint ht.1).trans_lt codeG_three_quarters_lt
  have hp := codeP_lower ht.2
  have htprod : 21 / 16 ≤ t * (1 + t) := by nlinarith [ht.1]
  have hmul := mul_nonneg (sub_nonneg.mpr htprod) (show 0 ≤ codeP t by linarith)
  nlinarith

theorem codeExponent_strictAnti : StrictAntiOn codeExponent (Set.Icc (3 / 4 : ℝ) 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · intro t ht
    exact (hasDerivAt_codeExponent ht.1).continuousAt.continuousWithinAt
  · intro t ht
    exact codeExponent_deriv_neg (interior_subset ht)

theorem codeExponent_le {t : ℝ} (ht : t ∈ Set.Icc (3 / 4 : ℝ) 1) :
    codeExponent t ≤ 2 * alpha0 := by
  rw [← codeExponent_three_quarters]
  exact codeExponent_strictAnti.antitoneOn (by constructor <;> norm_num) ht ht.1

end OM.NNN8
