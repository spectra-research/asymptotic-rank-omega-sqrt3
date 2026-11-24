import Lib.OM.NNN11.Functions
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Analytic derivatives for the seven-symbol capacity and rectangular envelope. -/
noncomputable section
namespace OM.NNN11
set_option maxHeartbeats 2000000

def weightedKSlope (t : ℝ) : ℝ := codeK t - 4 * t * codeP t
def weightedKSecond (t : ℝ) : ℝ :=
  -8 * codeP t - 16 * t * Real.log 2 * codeP t * (1 - codeP t)
def capacitySlope (t : ℝ) : ℝ :=
  7 * weightedKSlope t - 13 / 2 * weightedKSlope (shortParam t)
def capacitySecond (t : ℝ) : ℝ :=
  7 * weightedKSecond t + 13 / 4 * weightedKSecond (shortParam t)
def innerFSlope (t : ℝ) : ℝ :=
  (-196 * t + 161 - capacitySlope t - 14 * innerF t) / denominator t
def innerGSlope (t : ℝ) : ℝ :=
  (-252 * t + 623 / 2 - capacitySlope t - 14 * innerG t) / denominator t
def innerFSecond (t : ℝ) : ℝ :=
  (-196 - capacitySecond t - 28 * innerFSlope t) / denominator t
def innerGSecond (t : ℝ) : ℝ :=
  (-252 - capacitySecond t - 28 * innerGSlope t) / denominator t

lemma hasDerivAt_codeK (t : ℝ) : HasDerivAt codeK (-4 * codeP t) t := by
  have he : HasDerivAt (fun x : ℝ => 4 * x - 9 / 2) 4 t := by
    convert! ((hasDerivAt_id t).const_mul 4).sub_const (9 / 2) using 1 <;> ring
  have hp := (HasDerivAt.const_rpow (by norm_num : (0 : ℝ) < 2) he).const_mul 6
  have hl := ((hasDerivAt_const t (1 : ℝ)).add hp).log (by dsimp; positivity)
  have hn : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  convert! (hasDerivAt_const t (Real.logb 2 7)).sub (hl.div_const (Real.log 2)) using 1
  dsimp [codeP]
  field_simp
  ring

lemma hasDerivAt_codeP (t : ℝ) :
    HasDerivAt codeP (4 * Real.log 2 * codeP t * (1 - codeP t)) t := by
  have he : HasDerivAt (fun x : ℝ => 4 * x - 9 / 2) 4 t := by
    convert! ((hasDerivAt_id t).const_mul 4).sub_const (9 / 2) using 1 <;> ring
  have hp := (HasDerivAt.const_rpow (by norm_num : (0 : ℝ) < 2) he).const_mul 6
  convert! hp.div ((hasDerivAt_const t (1 : ℝ)).add hp) (by dsimp; positivity) using 1
  dsimp [codeP]
  field_simp
  ring

lemma codeP_mem (t : ℝ) : codeP t ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · dsimp [codeP]; positivity
  · apply (div_le_one (by positivity : 0 < 1 + 6 * (2 : ℝ) ^ (4 * t - 9 / 2))).2
    linarith

lemma hasDerivAt_weightedK (t : ℝ) : HasDerivAt weightedK (weightedKSlope t) t := by
  convert! (hasDerivAt_id t).mul (hasDerivAt_codeK t) using 1 <;>
    simp [weightedK, weightedKSlope] <;> ring

lemma hasDerivAt_weightedKSlope (t : ℝ) :
    HasDerivAt weightedKSlope (weightedKSecond t) t := by
  convert! (hasDerivAt_codeK t).sub
    (((hasDerivAt_id t).mul (hasDerivAt_codeP t)).const_mul 4) using 1
  · funext x
    simp [weightedKSlope]
    ring
  · dsimp [weightedKSecond]
    ring

lemma hasDerivAt_shortParam (t : ℝ) : HasDerivAt shortParam (-1 / 2) t := by
  convert! ((hasDerivAt_const t (9 / 4 : ℝ)).sub (hasDerivAt_id t)).div_const 2 using 1 <;>
    simp [shortParam] <;> ring

lemma hasDerivAt_capacity (t : ℝ) : HasDerivAt capacity (capacitySlope t) t := by
  convert! ((hasDerivAt_weightedK t).const_mul 7).add
    (((hasDerivAt_weightedK (shortParam t)).comp t (hasDerivAt_shortParam t)).const_mul 13)
    using 1 <;> simp [capacity, capacitySlope] <;> ring

lemma hasDerivAt_capacitySlope (t : ℝ) :
    HasDerivAt capacitySlope (capacitySecond t) t := by
  convert! ((hasDerivAt_weightedKSlope t).const_mul 7).sub
    (((hasDerivAt_weightedKSlope (shortParam t)).comp t (hasDerivAt_shortParam t)).const_mul
      (13 / 2)) using 1 <;> simp [capacitySlope, capacitySecond] <;> ring

lemma hasDerivAt_denominator (t : ℝ) : HasDerivAt denominator 14 t := by
  convert! (hasDerivAt_const t (196 : ℝ)).add ((hasDerivAt_id t).const_mul 14) using 1 <;>
    simp [denominator]

lemma hasDerivAt_numeratorF (t : ℝ) :
    HasDerivAt numeratorF (-196 * t + 161 - capacitySlope t) t := by
  convert! (((((hasDerivAt_id t).pow 2).const_mul (-98)).add
    ((hasDerivAt_id t).const_mul 161)).add_const (1953 / 8)).sub
    (hasDerivAt_capacity t) using 1 <;> simp [numeratorF] <;> ring

lemma hasDerivAt_numeratorG (t : ℝ) :
    HasDerivAt numeratorG (-252 * t + 623 / 2 - capacitySlope t) t := by
  convert! (((((hasDerivAt_id t).pow 2).const_mul (-126)).add
    ((hasDerivAt_id t).const_mul (623 / 2))).add_const (189 / 4)).sub
    (hasDerivAt_capacity t) using 1 <;> simp [numeratorG] <;> ring

lemma hasDerivAt_innerF {t : ℝ} (ht : 0 ≤ t) : HasDerivAt innerF (innerFSlope t) t := by
  have hd := (denominator_pos ht).ne'
  convert! (hasDerivAt_numeratorF t).div (hasDerivAt_denominator t) hd using 1
  dsimp [innerFSlope, innerF]
  field_simp <;> ring

lemma hasDerivAt_innerG {t : ℝ} (ht : 0 ≤ t) : HasDerivAt innerG (innerGSlope t) t := by
  have hd := (denominator_pos ht).ne'
  convert! (hasDerivAt_numeratorG t).div (hasDerivAt_denominator t) hd using 1
  dsimp [innerGSlope, innerG]
  field_simp <;> ring

lemma hasDerivAt_innerFSlope {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt innerFSlope (innerFSecond t) t := by
  have hd := (denominator_pos ht).ne'
  have hn := ((((hasDerivAt_id t).const_mul (-196)).add_const 161).sub
    (hasDerivAt_capacitySlope t)).sub ((hasDerivAt_innerF ht).const_mul 14)
  convert! hn.div (hasDerivAt_denominator t) hd using 1
  dsimp [innerFSecond, innerFSlope]
  field_simp
  ring

lemma hasDerivAt_innerGSlope {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt innerGSlope (innerGSecond t) t := by
  have hd := (denominator_pos ht).ne'
  have hn := ((((hasDerivAt_id t).const_mul (-252)).add_const (623 / 2)).sub
    (hasDerivAt_capacitySlope t)).sub ((hasDerivAt_innerG ht).const_mul 14)
  convert! hn.div (hasDerivAt_denominator t) hd using 1
  dsimp [innerGSecond, innerGSlope]
  field_simp
  ring

lemma weightedKSecond_bounds {t : ℝ} (ht : t ∈ Set.Icc (1 / 4 : ℝ) 1) :
    -11 ≤ weightedKSecond t ∧ weightedKSecond t ≤ 0 := by
  have hp := codeP_mem t
  have hl0 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hl1 : Real.log 2 ≤ 3 / 4 := by linarith [Real.log_two_lt_d9]
  have hpp0 : 0 ≤ codeP t * (1 - codeP t) := mul_nonneg hp.1 (sub_nonneg.mpr hp.2)
  have hpp1 : codeP t * (1 - codeP t) ≤ 1 / 4 := by nlinarith [sq_nonneg (codeP t - 1 / 2)]
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have htl : t * Real.log 2 ≤ 3 / 4 :=
    (mul_le_mul_of_nonneg_right ht.2 hl0).trans (by simpa using! hl1)
  have hbound := mul_le_mul htl hpp1 hpp0 (by norm_num : (0 : ℝ) ≤ 3 / 4)
  have hpos := mul_nonneg (mul_nonneg ht0 hl0) hpp0
  dsimp [weightedKSecond]
  constructor <;> nlinarith

theorem weightedK_concave : ConcaveOn ℝ (Set.Icc (1 / 4 : ℝ) 1) weightedK := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _)
    (fun t _ => (hasDerivAt_weightedK t).continuousAt.continuousWithinAt)
    (fun t _ => (hasDerivAt_weightedK t).hasDerivWithinAt)
    (fun t _ => (hasDerivAt_weightedKSlope t).hasDerivWithinAt)
  intro t ht
  exact (weightedKSecond_bounds (interior_subset ht)).2

lemma capacitySecond_bounds {t : ℝ} (ht : t ∈ Set.Icc (1 / 4 : ℝ) 1) :
    -451 / 4 ≤ capacitySecond t ∧ capacitySecond t ≤ 0 := by
  have h := weightedKSecond_bounds ht
  have hv := weightedKSecond_bounds (shortParam_mem ht)
  dsimp [capacitySecond]
  constructor <;> linarith

theorem capacity_concave : ConcaveOn ℝ (Set.Icc (1 / 4 : ℝ) 1) capacity := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _)
    (fun t _ => (hasDerivAt_capacity t).continuousAt.continuousWithinAt)
    (fun t _ => (hasDerivAt_capacity t).hasDerivWithinAt)
    (fun t _ => (hasDerivAt_capacitySlope t).hasDerivWithinAt)
  intro t ht
  exact (capacitySecond_bounds (interior_subset ht)).2

/-- The second concave function used to symmetrise the short parameters. -/
theorem inner_quadratic_concave :
    ConcaveOn ℝ (Set.Icc (1 / 4 : ℝ) 1) (fun t => -56 * t ^ 2 - 13 / 2 * weightedK t) := by
  have hd (t : ℝ) : HasDerivAt (fun t => -56 * t ^ 2 - 13 / 2 * weightedK t)
      (-112 * t - 13 / 2 * weightedKSlope t) t := by
    convert! (((hasDerivAt_id t).pow 2).const_mul (-56)).sub
      ((hasDerivAt_weightedK t).const_mul (13 / 2)) using 1 <;> simp only [id_eq] <;> ring
  have hdd (t : ℝ) : HasDerivAt (fun t => -112 * t - 13 / 2 * weightedKSlope t)
      (-112 - 13 / 2 * weightedKSecond t) t := by
    convert! ((hasDerivAt_id t).const_mul (-112)).sub
      ((hasDerivAt_weightedKSlope t).const_mul (13 / 2)) using 1 <;> ring
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _)
    (fun t _ => (hd t).continuousAt.continuousWithinAt)
    (fun t _ => (hd t).hasDerivWithinAt) (fun t _ => (hdd t).hasDerivWithinAt)
  intro t ht
  linarith [(weightedKSecond_bounds (interior_subset ht)).1]

end OM.NNN11
