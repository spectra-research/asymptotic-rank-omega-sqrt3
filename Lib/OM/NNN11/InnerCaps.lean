import Lib.OM.NNN11.Bounds

/-! The six inner rate-cap inequalities, proved analytically without cells. -/
noncomputable section
namespace OM.NNN11
set_option maxHeartbeats 2000000

def centralExcess (z t : ℝ) : ℝ :=
  70 * (innerF t - z * innerG t - (9 / 4 - t) * (1 - z)) +
    7 * (1 - z) * (codeK t - Real.logb 2 7)

def shortExcess (q b z t u : ℝ) : ℝ :=
  q * (innerF t - z * innerG t - 9 / 4 + u + t * z) +
    b * (1 - z) * (codeK u - Real.logb 2 7)

lemma hasDerivAt_centralExcess {z t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (centralExcess z)
      (70 * (innerFSlope t - z * innerGSlope t) + (1 - z) * (70 - 28 * codeP t)) t := by
  have hd := (((hasDerivAt_innerF ht).sub ((hasDerivAt_innerG ht).const_mul z)).sub
    (((hasDerivAt_const t (9 / 4 : ℝ)).sub (hasDerivAt_id t)).mul_const (1 - z))).const_mul 70
  convert! hd.add (((hasDerivAt_codeK t).sub_const (Real.logb 2 7)).const_mul (7 * (1 - z)))
    using 1 <;> (try dsimp [centralExcess]) <;> ring

lemma centralExcess_monotone {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) (1 / 5)) :
    MonotoneOn (centralExcess z) (Set.Icc (1 / 4 : ℝ) 1) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    (fun t ht => (hasDerivAt_centralExcess (z := z) (by linarith [ht.1])).continuousAt.continuousWithinAt)
    (fun t ht => (hasDerivAt_centralExcess (z := z)
      (by have := interior_subset ht; linarith [this.1])).differentiableAt.differentiableWithinAt)
  intro t ht
  have ht' := interior_subset ht
  rw [(hasDerivAt_centralExcess (z := z) (by linarith [ht'.1])).deriv]
  have hf := (innerSlope_bounds ht').1.1
  have hg := (innerSlope_bounds ht').2
  have hp := codeP_upper ht'.2
  have hzg := mul_le_mul hz.2 hg.2 hg.1 (by norm_num : (0 : ℝ) ≤ 1 / 5)
  have hprod := mul_le_mul (show (4 / 5 : ℝ) ≤ 1 - z by linarith [hz.2])
    (show (140 / 3 : ℝ) ≤ 70 - 28 * codeP t by linarith) (by norm_num : (0 : ℝ) ≤ 140 / 3)
    (show 0 ≤ 1 - z by linarith [hz.2])
  nlinarith

lemma centralExcess_endpoints : centralExcess 0 1 ≤ 0 ∧ centralExcess (1 / 5) 1 ≤ 0 := by
  have hk := codeK_one_bounds.2
  have hv := codeK_five_eighths_lower
  have hl := log_seven_bounds.1
  norm_num [centralExcess, innerF, innerG, numeratorF, numeratorG,
    denominator, capacity, weightedK, shortParam]
  constructor <;> linarith

lemma affine_cone_le {f : ℝ → ℝ}
    (hf : ∀ z, f z = (1 - 5 * z) * f 0 + (5 * z) * f (1 / 5))
    (h0 : f 0 ≤ 0) (h1 : f (1 / 5) ≤ 0)
    {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) (1 / 5)) : f z ≤ 0 := by
  rw [hf z]
  exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos (by linarith [hz.2]) h0)
    (mul_nonpos_of_nonneg_of_nonpos (by linarith [hz.1]) h1)

theorem centralExcess_nonpos {t z : ℝ}
    (ht : t ∈ Set.Icc (1 / 4 : ℝ) 1) (hz : z ∈ Set.Icc (0 : ℝ) (1 / 5)) :
    centralExcess z t ≤ 0 := by
  refine (centralExcess_monotone hz ht (by norm_num) ht.2).trans ?_
  apply affine_cone_le (f := fun z => centralExcess z 1) _
    centralExcess_endpoints.1 centralExcess_endpoints.2 hz
  intro z
  dsimp [centralExcess]
  ring

lemma gap_add_upper {t : ℝ} (ht : t ∈ Set.Icc (1 / 4 : ℝ) 1) :
    innerF t - innerG t + t ≤ 65 / 48 := by
  rw [innerF_sub_innerG (by linarith [ht.1])]
  have hd : 0 < 16 * (t + 14) := by linarith [ht.1]
  have hq : (4 * t - 9) * (8 * t - 25) / (16 * (t + 14)) ≤ 65 / 48 - t := by
    apply (div_le_iff₀ hd).2
    have hs : t ^ 2 ≤ t := by nlinarith [ht.1, ht.2]
    nlinarith [ht.2]
  linarith

lemma shortExcess_endpoint_bounds {t : ℝ} (ht : t ∈ Set.Icc (1 / 4 : ℝ) 1)
    {q b : ℝ} (hqb : (q = 70 ∧ b = 7) ∨ (q = 42 ∧ b = 6)) :
    shortExcess q b 0 t 1 ≤ 0 ∧ shortExcess q b (1 / 5) t 1 ≤ 0 := by
  have hf := innerF_upper ht
  have hg := gap_add_upper ht
  have hk := codeK_one_bounds.2
  have hl := log_seven_bounds.1
  rcases hqb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    norm_num [shortExcess] <;> constructor <;> linarith

lemma shortExcess_monotone {q b z t : ℝ} (hb : 0 ≤ b) (hq : 4 * b ≤ q)
    (hz : z ∈ Set.Icc (0 : ℝ) (1 / 5)) : Monotone (shortExcess q b z t) := by
  have hd (u : ℝ) : HasDerivAt (shortExcess q b z t) (q - 4 * b * (1 - z) * codeP u) u := by
    have h0 := (((hasDerivAt_const u (innerF t - z * innerG t - 9 / 4)).add
      (hasDerivAt_id u)).add_const (t * z)).const_mul q
    convert! h0.add (((hasDerivAt_codeK u).sub_const (Real.logb 2 7)).const_mul (b * (1 - z)))
      using 1 <;> (try dsimp [shortExcess]) <;> ring
  apply monotone_of_deriv_nonneg (fun u => (hd u).differentiableAt)
  intro u
  rw [(hd u).deriv]
  have hp := codeP_mem u
  have hprod := mul_le_mul (show 1 - z ≤ 1 by linarith [hz.1]) hp.2 hp.1
    (by norm_num : (0 : ℝ) ≤ 1)
  have hh := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 4 * b by linarith)
  nlinarith

theorem shortExcess_nonpos {t u z q b : ℝ}
    (ht : t ∈ Set.Icc (1 / 4 : ℝ) 1) (hu : u ≤ 1)
    (hz : z ∈ Set.Icc (0 : ℝ) (1 / 5))
    (hqb : (q = 70 ∧ b = 7) ∨ (q = 42 ∧ b = 6)) :
    shortExcess q b z t u ≤ 0 := by
  have hb : 0 ≤ b := by rcases hqb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num
  have hq : 4 * b ≤ q := by rcases hqb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num
  refine (shortExcess_monotone hb hq hz hu).trans ?_
  apply affine_cone_le (f := fun z => shortExcess q b z t 1) _
    (shortExcess_endpoint_bounds ht hqb).1 (shortExcess_endpoint_bounds ht hqb).2 hz
  intro z
  dsimp [shortExcess]
  ring

/-- The positive-part central rate fits the seven-cycle length. -/
theorem central_rate_cap {t z : ℝ}
    (ht : t ∈ Set.Icc (1 / 4 : ℝ) 1) (hz : z ∈ Set.Icc (0 : ℝ) (1 / 5)) :
    max 0 (70 * (innerF t - z * innerG t - (9 / 4 - t) * (1 - z)) +
      7 * (1 - z) * codeK t) ≤ 7 * (1 - z) * Real.logb 2 7 := by
  have hh := centralExcess_nonpos ht hz
  dsimp [centralExcess] at hh
  apply max_le
  · exact mul_nonneg (by linarith [hz.2]) (by linarith [log_seven_bounds.1])
  · nlinarith

/-- The positive-part rate on either short party fits its actual cycle length. -/
theorem short_rate_cap {t u z q b : ℝ}
    (ht : t ∈ Set.Icc (1 / 4 : ℝ) 1) (hu : u ≤ 1)
    (hz : z ∈ Set.Icc (0 : ℝ) (1 / 5))
    (hqb : (q = 70 ∧ b = 7) ∨ (q = 42 ∧ b = 6)) :
    max 0 (q * (innerF t - z * innerG t - 9 / 4 + u + t * z) +
      b * (1 - z) * codeK u) ≤ b * (1 - z) * Real.logb 2 7 := by
  have hh := shortExcess_nonpos ht hu hz hqb
  have hb : 0 ≤ b := by rcases hqb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num
  dsimp [shortExcess] at hh
  apply max_le
  · exact mul_nonneg (mul_nonneg hb (by linarith [hz.2])) (by linarith [log_seven_bounds.1])
  · nlinarith

end OM.NNN11
