import Lib.OM.NNN36.TriangleBound
import Lib.OM.PolMulRect.Flat
import PLATFORM.Statements.«R115.5»

/-! # The cubic region of exact asymptotic rank -/

namespace OM.NNN36

open P2M.R115

/-- At the base point with coordinate `x`, the cubic test puts the three
distances on the flat branch of the rectangular matrix multiplication bound. -/
private theorem flat_cost {c x : ℝ} {q : ℂ} (hc : 0 < c) (hx : x ∈ Set.Ioo 0 1)
    (hhalf : 1/2 ≤ x) (htest : (x-q.re)^2 + q.im^2 ≤ x^2*(1-x)^2) :
    let z := (c : ℂ)*(x : ℂ)
    OmegaBound.omegaRect3 ℂ (dist z 0) (dist z (c : ℂ)) (dist z ((c : ℂ)*q)) = c := by
  let z := (c : ℂ)*(x : ℂ)
  let r := dist z ((c : ℂ)*q)
  have hx' := sub_nonneg.mpr hx.2.le
  have h₁ : dist z 0 = c*x := by
    rw [dist_zero_right, show z = ((c*x : ℝ) : ℂ) by push_cast; rfl]
    exact Complex.norm_of_nonneg (mul_nonneg hc.le hx.1.le)
  have h₂ : dist z (c : ℂ) = c*(1-x) := by
    rw [dist_comm, dist_eq_norm, show (c : ℂ) - z = ((c*(1-x) : ℝ) : ℂ) by
      dsimp [z]; push_cast; ring]
    exact Complex.norm_of_nonneg (mul_nonneg hc.le hx')
  have height : ‖(x : ℂ)-q‖ ≤ x*(1-x) := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hx.1.le hx')).mp
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, zero_sub]
    nlinarith only [htest]
  have hr : r ≤ c*(x*(1-x)) := by
    dsimp only [r, z]
    rw [dist_eq_norm, ← mul_sub, norm_mul, Complex.norm_of_nonneg hc.le]
    exact mul_le_mul_of_nonneg_left height hc.le
  have hsmall : r ≤ c*(1-x) := hr.trans (mul_le_mul_of_nonneg_left
    (mul_le_of_le_one_left hx' hx.2.le) hc.le)
  have hsort : c*(1-x) ≤ c*x := mul_le_mul_of_nonneg_left (by linarith) hc.le
  have hsum : c*x + c*(1-x) = c := by ring
  have hflat : r * (c*x + c*(1-x)) ≤ (c*x) * (c*(1-x)) := by
    rw [hsum]
    exact (mul_le_mul_of_nonneg_right hr hc.le).trans_eq (by ring)
  change OmegaBound.omegaRect3 ℂ (dist z 0) (dist z (c : ℂ)) r = c
  rw [h₁, h₂, PolMulRect.omegaRect3_eq_omegaRect,
    PolMulRect.omegaRect_eq_add ℂ dist_nonneg hsmall hsort hflat, hsum]

theorem proof_R115_5 : S_R115_5 := by
  intro n₁ n₂ n₃ h₁₂ h₂₃
  dsimp only
  intro ht
  let a := sideLog n₁
  let b := sideLog n₂
  let c := sideLog n₃
  let q := normalizedApex a b c
  change c < a+b at ht
  have hab : a ≤ b := sideLog_mono h₁₂
  have hbc : b ≤ c := sideLog_mono h₂₃
  have ha : 0 < a := by linarith
  have hc := (ha.trans_le hab).trans_le hbc
  obtain ⟨⟨hhalf,hlt⟩,_,_,_⟩ := apex_geometry ha hab hbc ht
  refine ⟨cubic_root ⟨(by norm_num : (0 : ℝ) < 1/2).trans_le hhalf,hlt⟩,?_⟩
  rintro x ⟨hx,he⟩ htest
  let z := (c : ℂ)*(x : ℂ)
  let V : Set ℂ := {0,(c : ℂ),(c : ℂ)*q}
  have hz : z ∈ convexHull ℝ V := by
    apply segment_subset_convexHull (x := (0 : ℂ)) (y := (c : ℂ)) (by simp [V]) (by simp [V])
    refine ⟨1-x,x,sub_nonneg.mpr hx.2.le,hx.1.le,by ring,?_⟩
    simp only [smul_zero,zero_add,Complex.real_smul]
    exact mul_comm _ _
  obtain ⟨y,_,hmin,hrank⟩ := proof_R115_4 n₁ n₂ n₃ h₁₂ h₂₃ ht
  have hlog : Real.logb 2 (formatRankSup n₁ n₂ n₃) ≤ c :=
    (hrank.trans (hmin z hz)).trans_eq (flat_cost hc hx (half_le_of_cubic hx he hhalf) htest)
  have hupper := (Real.logb_le_logb one_lt_two (formatRankSup_pos n₁ n₂ n₃)
    (show 0 < (n₃ : ℝ) by positivity)).mp hlog
  have hprod : (n₃ : ℕ) ≤ (n₁ : ℕ)*(n₂ : ℕ) := by
    change Real.logb 2 (n₃ : ℝ) < Real.logb 2 (n₁ : ℝ) + Real.logb 2 (n₂ : ℝ) at ht
    rw [← Real.logb_mul (by positivity : (n₁ : ℝ) ≠ 0) (by positivity : (n₂ : ℝ) ≠ 0)] at ht
    exact_mod_cast ((Real.logb_lt_logb_iff one_lt_two (by positivity) (by positivity)).mp ht).le
  have hlower := (format_bounds n₁ n₂ n₃).1
  rw [min_eq_left hprod] at hlower
  exact le_antisymm hupper hlower

end OM.NNN36

