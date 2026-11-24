import Lib.OM.NNN11.Bounds

/-! Analytic outer curvature: a single proof over the entire asymmetric interval. -/
noncomputable section
namespace OM.NNN11
set_option maxHeartbeats 3000000

def outerDSlope (t : ℝ) : ℝ := 159 / 100 - 41 / 100 * innerGSlope t
def outerDSecond (t : ℝ) : ℝ := -41 / 100 * innerGSecond t
def outerP (t : ℝ) : ℝ :=
  6 * (2 : ℝ) ^ (2 * outerD t) / (1 + 6 * (2 : ℝ) ^ (2 * outerD t))
def fullSlope (t : ℝ) : ℝ :=
  70 * (-59 / 100 + 41 / 100 * innerFSlope t) + 14 * outerP t * outerDSlope t
def fullSecond (t : ℝ) : ℝ :=
  70 * (41 / 100 * innerFSecond t) + 14 * outerP t * outerDSecond t +
    28 * Real.log 2 * outerP t * (1 - outerP t) * outerDSlope t ^ 2

lemma outerP_mem (t : ℝ) : outerP t ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · dsimp [outerP]; positivity
  · apply (div_le_one (by positivity : 0 < 1 + 6 * (2 : ℝ) ^ (2 * outerD t))).2
    linarith

lemma hasDerivAt_outerD {t : ℝ} (ht : 0 ≤ t) : HasDerivAt outerD (outerDSlope t) t := by
  convert! ((((hasDerivAt_id t).const_mul 2).sub_const (9 / 4)).const_mul (59 / 100)).add
    (((hasDerivAt_id t).sub (hasDerivAt_innerG ht)).const_mul (41 / 100)) using 1 <;>
    (try dsimp [outerD, outerDSlope]) <;> ring

lemma hasDerivAt_outerDSlope {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt outerDSlope (outerDSecond t) t := by
  convert! (hasDerivAt_const t (159 / 100 : ℝ)).sub
    ((hasDerivAt_innerGSlope ht).const_mul (41 / 100)) using 1 <;>
    (try dsimp [outerDSlope, outerDSecond]) <;> ring

lemma hasDerivAt_outerP {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt outerP (2 * Real.log 2 * outerDSlope t * outerP t * (1 - outerP t)) t := by
  have hp := (HasDerivAt.const_rpow (by norm_num : (0 : ℝ) < 2)
    ((hasDerivAt_outerD ht).const_mul 2)).const_mul 6
  convert! hp.div ((hasDerivAt_const t (1 : ℝ)).add hp) (by dsimp; positivity) using 1
  dsimp [outerP]
  field_simp
  ring

lemma hasDerivAt_fullMoment {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt fullMoment (fullSlope t) t := by
  have ha : HasDerivAt outerA (-59 / 100 + 41 / 100 * innerFSlope t) t := by
    convert! (((hasDerivAt_const t (9 / 4 : ℝ)).sub (hasDerivAt_id t)).const_mul (59 / 100)).add
      ((hasDerivAt_innerF ht).const_mul (41 / 100)) using 1 <;> (try dsimp [outerA]) <;> ring
  have hp := (HasDerivAt.const_rpow (by norm_num : (0 : ℝ) < 2)
    ((hasDerivAt_outerD ht).const_mul 2)).const_mul 6
  have hl := (((hasDerivAt_const t (1 : ℝ)).add hp).log (by dsimp; positivity)).div_const (Real.log 2)
  have hn : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  convert! (ha.const_mul 70).add ((hl.sub_const (Real.logb 2 7)).const_mul 7) using 1
  dsimp [fullSlope, outerP]
  field_simp
  ring

lemma hasDerivAt_fullSlope {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt fullSlope (fullSecond t) t := by
  have h1 := ((hasDerivAt_const t (-59 / 100 : ℝ)).add
    ((hasDerivAt_innerFSlope ht).const_mul (41 / 100))).const_mul 70
  have h2 := ((hasDerivAt_outerP ht).mul (hasDerivAt_outerDSlope ht)).const_mul 14
  convert! h1.add h2 using 1
  · funext x
    dsimp [fullSlope]
    ring
  · dsimp [fullSecond]
    ring

lemma outerD_derivative_bounds {t : ℝ} (ht : t ∈ Set.Icc (1 / 4 : ℝ) 1) :
    (0 ≤ outerDSlope t ∧ outerDSlope t ≤ 159 / 100) ∧
      (0 ≤ outerDSecond t ∧ outerDSecond t ≤ 123 / 200) := by
  have h := (innerSlope_bounds ht).2
  have hh := (innerSecond_bounds ht).2
  dsimp [outerDSlope, outerDSecond]
  constructor <;> constructor <;> linarith

theorem fullSlope_upper {t : ℝ} (ht : t ∈ Set.Icc (1 / 4 : ℝ) 1) : fullSlope t ≤ -9 := by
  have hf := (innerSlope_bounds ht).1.2
  have hp := outerP_mem t
  have hd := (outerD_derivative_bounds ht).1
  have hm := mul_le_mul hp.2 hd.2 hd.1 (by norm_num : (0 : ℝ) ≤ 1)
  dsimp [fullSlope]
  nlinarith

theorem fullSecond_upper {t : ℝ} (ht : t ∈ Set.Icc (1 / 4 : ℝ) 1) : fullSecond t ≤ 15 := by
  have hf := (innerSecond_bounds ht).1
  have hp := outerP_mem t
  have hd := outerD_derivative_bounds ht
  have hpd := mul_le_mul hp.2 hd.2.2 hd.2.1 (by norm_num : (0 : ℝ) ≤ 1)
  have hpp : outerP t * (1 - outerP t) ≤ 1 / 4 := by nlinarith [sq_nonneg (outerP t - 1 / 2)]
  have hpp0 : 0 ≤ outerP t * (1 - outerP t) := mul_nonneg hp.1 (by linarith [hp.2])
  have hd2 : outerDSlope t ^ 2 ≤ (159 / 100 : ℝ) ^ 2 := by nlinarith [hd.1.1, hd.1.2]
  have hl : Real.log 2 ≤ 3 / 4 := by linarith [Real.log_two_lt_d9]
  have hprod := mul_le_mul hl hpp hpp0 (by norm_num : (0 : ℝ) ≤ 3 / 4)
  have hlast := mul_le_mul hprod hd2 (sq_nonneg _) (by norm_num : (0 : ℝ) ≤ (3 / 4) * (1 / 4))
  dsimp [fullSecond]
  nlinarith

theorem full_weighted_curvature {t : ℝ} (ht : t ∈ Set.Icc (1 / 4 : ℝ) 1) :
    2 * fullSlope t + t * fullSecond t ≤ -3 := by
  have hs := fullSlope_upper ht
  have hsecond := mul_le_mul_of_nonneg_left (fullSecond_upper ht)
    (show 0 ≤ t by linarith [ht.1])
  nlinarith [ht.2]

def fullRate (b t : ℝ) : ℝ := max 0 (70 * b - fullMoment t)
def finalRate (b t : ℝ) : ℝ := max 0 (42 * b - lastMoment t)

theorem fullWeighted_convex (b : ℝ) :
    ConvexOn ℝ (Set.Icc (1 / 4 : ℝ) 1) (fun t => t * fullRate b t) := by
  have hd {t : ℝ} (ht : 0 ≤ t) : HasDerivAt (fun t => t * (70 * b - fullMoment t))
      (70 * b - fullMoment t - t * fullSlope t) t := by
    convert! (hasDerivAt_id t).mul ((hasDerivAt_const t (70 * b)).sub (hasDerivAt_fullMoment ht))
      using 1 <;> (try dsimp) <;> ring
  have hdd {t : ℝ} (ht : 0 ≤ t) : HasDerivAt
      (fun t => 70 * b - fullMoment t - t * fullSlope t)
      (-2 * fullSlope t - t * fullSecond t) t := by
    convert! ((hasDerivAt_const t (70 * b)).sub (hasDerivAt_fullMoment ht)).sub
      ((hasDerivAt_id t).mul (hasDerivAt_fullSlope ht)) using 1 <;> (try dsimp) <;> ring
  have hc : ConvexOn ℝ (Set.Icc (1 / 4 : ℝ) 1) (fun t => t * (70 * b - fullMoment t)) := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
      (fun t ht => (hd (by linarith [ht.1])).continuousAt.continuousWithinAt)
      (fun t ht => (hd (by have := interior_subset ht; linarith [this.1])).hasDerivWithinAt)
      (fun t ht => (hdd (by have := interior_subset ht; linarith [this.1])).hasDerivWithinAt)
    intro t ht
    linarith [full_weighted_curvature (interior_subset ht)]
  have he : Set.EqOn (fun t => t * fullRate b t)
      ((fun _ : ℝ => (0 : ℝ)) ⊔ (fun t => t * (70 * b - fullMoment t)))
      (Set.Icc (1 / 4 : ℝ) 1) := by
    intro t ht
    dsimp [fullRate]
    rw [mul_max_of_nonneg _ _ (by linarith [ht.1]), mul_zero]
  exact ((convexOn_const (0 : ℝ) (convex_Icc (1 / 4 : ℝ) 1)).sup hc).congr he.symm

theorem lastWeighted_convex (b : ℝ) :
    ConvexOn ℝ (Set.Icc (1 / 4 : ℝ) 1) (fun t => t * finalRate b t) := by
  let f := fun t : ℝ => (42 * b - 189 / 2) * t + 42 * t ^ 2 + 6 * weightedK t
  have hd (t : ℝ) : HasDerivAt f (42 * b - 189 / 2 + 84 * t + 6 * weightedKSlope t) t := by
    convert! (((hasDerivAt_id t).const_mul (42 * b - 189 / 2)).add
      (((hasDerivAt_id t).pow 2).const_mul 42)).add ((hasDerivAt_weightedK t).const_mul 6)
      using 1 <;> (try dsimp [f]) <;> ring
  have hdd (t : ℝ) : HasDerivAt
      (fun t => 42 * b - 189 / 2 + 84 * t + 6 * weightedKSlope t)
      (84 + 6 * weightedKSecond t) t := by
    convert! ((hasDerivAt_const t (42 * b - 189 / 2)).add ((hasDerivAt_id t).const_mul 84)).add
      ((hasDerivAt_weightedKSlope t).const_mul 6) using 1 <;> (try dsimp) <;> ring
  have hc : ConvexOn ℝ (Set.Icc (1 / 4 : ℝ) 1) f := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
      (fun t _ => (hd t).continuousAt.continuousWithinAt)
      (fun t _ => (hd t).hasDerivWithinAt) (fun t _ => (hdd t).hasDerivWithinAt)
    intro t ht
    linarith [(weightedKSecond_bounds (interior_subset ht)).1]
  have he : Set.EqOn (fun t => t * finalRate b t) ((fun _ : ℝ => (0 : ℝ)) ⊔ f)
      (Set.Icc (1 / 4 : ℝ) 1) := by
    intro t ht
    dsimp [finalRate]
    rw [mul_max_of_nonneg _ _ (by linarith [ht.1]), mul_zero]
    congr 1
    dsimp [f, lastMoment, weightedK]
    ring
  exact ((convexOn_const (0 : ℝ) (convex_Icc (1 / 4 : ℝ) 1)).sup hc).congr he.symm

end OM.NNN11
