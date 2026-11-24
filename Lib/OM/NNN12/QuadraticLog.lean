import Lib.OM.NNN12.NearNumerics
import Mathlib.Analysis.Convex.Deriv

/-! Global quadratic upper bounds for logarithmic moments, obtained from
the variance bound `p (1-p) ≤ 1/4`. These are analytic bounds on all of ℝ. -/
noncomputable section
namespace OM.NNN12
set_option maxHeartbeats 3000000

def mixedLog (q k x : ℝ) : ℝ :=
  Real.logb 2 (1 + (q - 1) * (2 : ℝ) ^ (k * x)) - Real.logb 2 q
def mixedProbability (q k x : ℝ) : ℝ :=
  (q - 1) * (2 : ℝ) ^ (k * x) / (1 + (q - 1) * (2 : ℝ) ^ (k * x))

lemma mixedProbability_mem {q : ℝ} (hq : 1 ≤ q) (k x : ℝ) :
    mixedProbability q k x ∈ Set.Icc (0 : ℝ) 1 := by
  have hq0 : 0 ≤ q - 1 := by linarith
  have hd : 0 < 1 + (q - 1) * (2 : ℝ) ^ (k * x) := by positivity
  constructor
  · unfold mixedProbability; positivity
  · apply (div_le_one hd).2
    linarith

lemma hasDerivAt_mixedLog {q : ℝ} (hq : 1 ≤ q) (k x : ℝ) :
    HasDerivAt (mixedLog q k) (k * mixedProbability q k x) x := by
  have hq0 : 0 ≤ q - 1 := by linarith
  have he := (HasDerivAt.const_rpow (by norm_num : (0 : ℝ) < 2)
    ((hasDerivAt_id x).const_mul k)).const_mul (q - 1)
  have hl := (((hasDerivAt_const x (1 : ℝ)).add he).log (by dsimp; positivity)).div_const (Real.log 2)
  have hn : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  convert! hl.sub_const (Real.logb 2 q) using 1
  dsimp [mixedLog, mixedProbability, Real.logb]
  field_simp
  ring

lemma hasDerivAt_mixedProbability {q : ℝ} (hq : 1 ≤ q) (k x : ℝ) :
    HasDerivAt (mixedProbability q k)
      (k * Real.log 2 * mixedProbability q k x * (1 - mixedProbability q k x)) x := by
  have hq0 : 0 ≤ q - 1 := by linarith
  have he := (HasDerivAt.const_rpow (by norm_num : (0 : ℝ) < 2)
    ((hasDerivAt_id x).const_mul k)).const_mul (q - 1)
  have hd : 1 + (q - 1) * (2 : ℝ) ^ (k * x) ≠ 0 := by positivity
  convert! he.div ((hasDerivAt_const x (1 : ℝ)).add he) hd using 1
  dsimp [mixedProbability]
  field_simp
  ring

lemma mixedLog_second_upper {q : ℝ} (hq : 1 ≤ q) (k x : ℝ) :
    k ^ 2 * Real.log 2 * mixedProbability q k x * (1 - mixedProbability q k x) ≤ 7 / 40 * k ^ 2 := by
  have hp := mixedProbability_mem hq k x
  have hv : 0 ≤ mixedProbability q k x * (1 - mixedProbability q k x) := mul_nonneg hp.1 (by linarith [hp.2])
  have hb : mixedProbability q k x * (1 - mixedProbability q k x) ≤ 1 / 4 := by
    nlinarith [sq_nonneg (mixedProbability q k x - 1 / 2)]
  have hl : Real.log 2 ≤ 7 / 10 := by linarith [Real.log_two_lt_d9]
  have hh := mul_le_mul_of_nonneg_left
    (mul_le_mul hl hb hv (by norm_num : (0 : ℝ) ≤ 7 / 10)) (sq_nonneg k)
  nlinarith only [hh]

lemma convex_tangent_univ {f : ℝ → ℝ} {d c : ℝ} (hc : ConvexOn ℝ Set.univ f)
    (hd : HasDerivAt f d c) (x : ℝ) : f c + d * (x - c) ≤ f x := by
  rcases lt_trichotomy c x with h | h | h
  · have hh := hc.le_slope_of_hasDerivAt (Set.mem_univ _) (Set.mem_univ _) h hd
    rw [slope_def_field] at hh
    have hh' := (le_div_iff₀ (sub_pos.mpr h)).1 hh
    linarith
  · subst x; simp
  · have hh := hc.slope_le_of_hasDerivAt (Set.mem_univ _) (Set.mem_univ _) h hd
    rw [slope_def_field] at hh
    have hh' := (div_le_iff₀ (sub_pos.mpr h)).1 hh
    nlinarith

theorem quadratic_upper_of_second {f f' f'' : ℝ → ℝ} {C : ℝ}
    (hd : ∀ x, HasDerivAt f (f' x) x) (hdd : ∀ x, HasDerivAt f' (f'' x) x)
    (hC : ∀ x, f'' x ≤ 2 * C) (c x : ℝ) :
    f x ≤ f c + f' c * (x - c) + C * (x - c) ^ 2 := by
  let g := fun y => C * (y - c) ^ 2 - f y
  let g' := fun y => 2 * C * (y - c) - f' y
  have hg (y) : HasDerivAt g (g' y) y := by
    convert! ((((hasDerivAt_id y).sub_const c).pow 2).const_mul C).sub (hd y) using 1 <;>
      (try dsimp [g, g']) <;> ring
  have hgg (y) : HasDerivAt g' (2 * C - f'' y) y := by
    convert! (((hasDerivAt_id y).sub_const c).const_mul (2 * C)).sub (hdd y) using 1 <;>
      (try dsimp [g']) <;> ring
  have hc : ConvexOn ℝ Set.univ g := by
    apply convexOn_of_hasDerivWithinAt2_nonneg convex_univ
      (fun y _ => (hg y).continuousAt.continuousWithinAt)
      (fun y _ => (hg y).hasDerivWithinAt) (fun y _ => (hgg y).hasDerivWithinAt)
    intro y _
    linarith [hC y]
  have hh := convex_tangent_univ hc (hg c) x
  dsimp [g, g'] at hh
  nlinarith

theorem mixedLog_quadratic {q : ℝ} (hq : 1 ≤ q) (k c x : ℝ) :
    mixedLog q k x ≤ mixedLog q k c + k * mixedProbability q k c * (x - c) +
      (7 / 80 * k ^ 2) * (x - c) ^ 2 := by
  have hdd (y) : HasDerivAt (fun z => k * mixedProbability q k z)
      (k ^ 2 * Real.log 2 * mixedProbability q k y * (1 - mixedProbability q k y)) y := by
    convert! (hasDerivAt_mixedProbability hq k y).const_mul k using 1 <;> ring
  exact quadratic_upper_of_second (hasDerivAt_mixedLog hq k) hdd
    (fun y => by nlinarith only [mixedLog_second_upper hq k y]) c x

lemma mixedLog_mono {q k : ℝ} (hq : 1 ≤ q) (hk : 0 ≤ k) : Monotone (mixedLog q k) := by
  apply monotone_of_hasDerivAt_nonneg (hasDerivAt_mixedLog hq k)
  intro x
  exact mul_nonneg hk (mixedProbability_mem hq k x).1

lemma mixedLog_lipschitz {q k x y : ℝ} (hq : 1 ≤ q) (hk : 0 ≤ k) (hxy : x ≤ y) :
    mixedLog q k y - mixedLog q k x ≤ k * (y - x) := by
  have hd (z) : HasDerivAt (fun z => k * z - mixedLog q k z)
      (k - k * mixedProbability q k z) z := by
    simpa using! ((hasDerivAt_id z).const_mul k).sub (hasDerivAt_mixedLog hq k z)
  have hm := monotone_of_hasDerivAt_nonneg hd (fun z => by
    change 0 ≤ k - k * mixedProbability q k z
    have hh := mul_le_mul_of_nonneg_left (mixedProbability_mem hq k z).2 hk
    nlinarith only [hh]) hxy
  linarith

lemma rounded_slope_error {u v ε x : ℝ} (hε : 0 ≤ ε) (h : |u - v| ≤ ε) :
    (u - v) * x ≤ ε / 2 * (1 + x ^ 2) := by
  have h1 := (abs_le.mp h).1
  have h2 := (abs_le.mp h).2
  by_cases hx : 0 ≤ x
  · have hh := mul_le_mul_of_nonneg_right h2 hx
    nlinarith [mul_nonneg hε (sq_nonneg (x - 1))]
  · have hh := mul_le_mul_of_nonpos_right h1 (le_of_not_ge hx)
    nlinarith [mul_nonneg hε (sq_nonneg (x + 1))]

end OM.NNN12
