import Mathlib
import Lib.OM.NNN18.Setup

/-!
* `concaveOn_ratPart`: on an interval where `β(y) = p + s y > 0` and `ρ β + 3σ ≤ 0`,
  `y ↦ a + b y + ρ/β + σ/β²` is concave (its second derivative is `2s²(ρβ+3σ)/β⁴`).
* `hinge`: `(y - H)_+²`, which is `C¹` with derivative `2 (y - H)_+`.
* `concaveOn_of_deriv_pieces`: a differentiable function whose derivative is antitone on
  `[l, m]` and on `[m, u]` is concave on `[l, u]`.
* `chord_of_concave`: concavity on `[-Y, Y]` gives the chord bound used in (7.2).
* `quad3_nonneg_of_minors`: a symmetric 3×3 matrix whose (1,1) entry, (1,2)-block determinant
  and full determinant are positive is positive semidefinite (LDLᵀ identity).
-/

noncomputable section
open Set
namespace OM.NNN18

/-- The rational part `a + b y + ρ/(p+sy) + σ/(p+sy)²`. -/
def ratPart (a b ρ σ p s y : ℝ) : ℝ := a + b * y + ρ / (p + s * y) + σ / (p + s * y) ^ 2

lemma hasDerivAt_ratPart (a b ρ σ p s y : ℝ) (hβ : p + s * y ≠ 0) :
    HasDerivAt (ratPart a b ρ σ p s)
      (b - ρ * s / (p + s * y) ^ 2 - 2 * σ * s / (p + s * y) ^ 3) y := by
  have hl : HasDerivAt (fun y => p + s * y) s y := by
    simpa using ((hasDerivAt_id y).const_mul s).const_add p
  have h1 := (hl.inv hβ).const_mul ρ
  have h2 := ((hl.pow 2).inv (pow_ne_zero 2 hβ)).const_mul σ
  have h0 : HasDerivAt (fun y => a + b * y) b y := by
    simpa using ((hasDerivAt_id y).const_mul b).const_add a
  have := (h0.add h1).add h2
  convert! this using 1
  simp only [Pi.pow_apply]
  field_simp
  ring

lemma hasDerivAt_ratPart' (b ρ σ p s y : ℝ) (hβ : p + s * y ≠ 0) :
    HasDerivAt (fun y => b - ρ * s / (p + s * y) ^ 2 - 2 * σ * s / (p + s * y) ^ 3)
      (2 * s ^ 2 * (ρ * (p + s * y) + 3 * σ) / (p + s * y) ^ 4) y := by
  have hl : HasDerivAt (fun y => p + s * y) s y := by
    simpa using ((hasDerivAt_id y).const_mul s).const_add p
  have h1 := ((hl.pow 2).inv (pow_ne_zero 2 hβ)).const_mul (ρ * s)
  have h2 := ((hl.pow 3).inv (pow_ne_zero 3 hβ)).const_mul (2 * σ * s)
  have := ((hasDerivAt_const y b).sub h1).sub h2
  convert! this using 1
  simp only [Pi.pow_apply]
  field_simp
  ring

/-- Concavity of a rational part on an interval where its curvature sign holds. -/
theorem concaveOn_ratPart {a b ρ σ p s l u : ℝ}
    (hpos : ∀ y ∈ Icc l u, 0 < p + s * y)
    (hsign : ∀ y ∈ Icc l u, ρ * (p + s * y) + 3 * σ ≤ 0) :
    ConcaveOn ℝ (Icc l u) (ratPart a b ρ σ p s) := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc l u)
    (f' := fun y => b - ρ * s / (p + s * y) ^ 2 - 2 * σ * s / (p + s * y) ^ 3)
    (f'' := fun y => 2 * s ^ 2 * (ρ * (p + s * y) + 3 * σ) / (p + s * y) ^ 4)
  · intro y hy
    exact (hasDerivAt_ratPart a b ρ σ p s y (hpos y hy).ne').continuousAt.continuousWithinAt
  · intro y hy
    have hy' := interior_subset hy
    exact (hasDerivAt_ratPart a b ρ σ p s y (hpos y hy').ne').hasDerivWithinAt
  · intro y hy
    have hy' := interior_subset hy
    exact (hasDerivAt_ratPart' b ρ σ p s y (hpos y hy').ne').hasDerivWithinAt
  · intro y hy
    have hy' := interior_subset hy
    have h4 : 0 < (p + s * y) ^ 4 := by have := hpos y hy'; positivity
    apply div_nonpos_of_nonpos_of_nonneg _ h4.le
    have := hsign y hy'
    have : 0 ≤ 2 * s ^ 2 := by positivity
    nlinarith

/-! ## The hinge `(y - H)_+²` -/

def hinge (H y : ℝ) : ℝ := (max (y - H) 0) ^ 2

lemma hasDerivAt_hinge (H y : ℝ) : HasDerivAt (hinge H) (2 * max (y - H) 0) y := by
  rcases lt_trichotomy y H with h | h | h
  · -- locally zero
    have hev : hinge H =ᶠ[nhds y] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds h] with w hw
      have hw' : w - H ≤ 0 := by linarith [Set.mem_Iio.1 hw]
      simp [hinge, max_eq_right hw']
    rw [max_eq_right (by linarith : y - H ≤ 0), mul_zero]
    exact (hasDerivAt_const y (0 : ℝ)).congr_of_eventuallyEq hev
  · subst h
    simp only [sub_self, max_self, mul_zero]
    rw [hasDerivAt_iff_isLittleO]
    simp only [hinge, sub_self, max_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, sub_zero, smul_zero]
    have hsq : (fun w => (w - y) ^ 2) =o[nhds y] fun w => w - y := by
      have := (Asymptotics.isLittleO_pow_id (𝕜 := ℝ) (by norm_num : 1 < 2)).comp_tendsto
        (tendsto_sub_nhds_zero_iff.2 (Filter.tendsto_id (x := nhds y)))
      simpa [Function.comp_def] using this
    refine Asymptotics.IsBigO.trans_isLittleO ?_ hsq
    refine Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun w => ?_)
    simp only [norm_pow, Real.norm_eq_abs, one_mul]
    rw [sq_abs, sq_abs]
    rcases le_total (w - y) 0 with hw | hw
    · rw [max_eq_right hw]; nlinarith [sq_nonneg (w - y)]
    · rw [max_eq_left hw]
  · have hev : hinge H =ᶠ[nhds y] fun w => (w - H) ^ 2 := by
      filter_upwards [Ioi_mem_nhds h] with w hw
      have hw' : 0 ≤ w - H := by linarith [Set.mem_Ioi.1 hw]
      simp [hinge, max_eq_left hw']
    rw [max_eq_left (by linarith : 0 ≤ y - H)]
    have := ((hasDerivAt_id y).sub_const H).pow 2
    refine (this.congr_deriv (by simp)).congr_of_eventuallyEq hev

/-- Antitone pieces glue. -/
lemma antitoneOn_glue {f : ℝ → ℝ} {l m u : ℝ} (h1 : AntitoneOn f (Icc l m))
    (h2 : AntitoneOn f (Icc m u)) (hlm : l ≤ m) (hmu : m ≤ u) : AntitoneOn f (Icc l u) := by
  intro x hx y hy hxy
  by_cases hxm : x ≤ m
  · by_cases hym : y ≤ m
    · exact h1 ⟨hx.1, hxm⟩ ⟨hy.1, hym⟩ hxy
    · exact (h2 ⟨le_refl m, hmu⟩ ⟨(not_le.1 hym).le, hy.2⟩ (not_le.1 hym).le).trans
        (h1 ⟨hx.1, hxm⟩ ⟨hlm, le_refl m⟩ hxm)
  · exact h2 ⟨(not_le.1 hxm).le, hx.2⟩ ⟨(not_le.1 hxm).le.trans hxy, hy.2⟩ hxy

/-- A function differentiable everywhere, whose derivative is antitone on `[l, u]`, is
concave on `[l, u]`. -/
lemma concaveOn_of_hasDerivAt_antitone {f f' : ℝ → ℝ} {l u : ℝ}
    (hd : ∀ y, HasDerivAt f (f' y) y) (hanti : AntitoneOn f' (Icc l u)) :
    ConcaveOn ℝ (Icc l u) f := by
  have hderiv : deriv f = f' := funext fun y => (hd y).deriv
  apply AntitoneOn.concaveOn_of_deriv (convex_Icc l u)
  · exact fun y _ => (hd y).continuousAt.continuousWithinAt
  · exact fun y _ => (hd y).differentiableAt.differentiableWithinAt
  · rw [hderiv]; exact hanti.mono interior_subset

/-- The chord bound from concavity on `[-Y, Y]`. -/
lemma chord_of_concave {f : ℝ → ℝ} {Y y : ℝ} (hY : 0 < Y) (hc : ConcaveOn ℝ (Icc (-Y) Y) f)
    (hy₁ : -Y ≤ y) (hy₂ : y ≤ Y) :
    (Y - y) / (2 * Y) * f (-Y) + (Y + y) / (2 * Y) * f Y ≤ f y := by
  have hY0 : Y ≠ 0 := hY.ne'
  have ha : 0 ≤ (Y - y) / (2 * Y) := div_nonneg (by linarith) (by linarith)
  have hb : 0 ≤ (Y + y) / (2 * Y) := div_nonneg (by linarith) (by linarith)
  have hab : (Y - y) / (2 * Y) + (Y + y) / (2 * Y) = 1 := by field_simp; ring
  have h := hc.2 (show -Y ∈ Icc (-Y) Y from ⟨le_refl _, by linarith⟩)
    (show Y ∈ Icc (-Y) Y from ⟨by linarith, le_refl _⟩) ha hb hab
  have hy : (Y - y) / (2 * Y) * (-Y) + (Y + y) / (2 * Y) * Y = y := by
    have h2Y : (2 * Y) ≠ 0 := by positivity
    have e : (Y - y) / (2 * Y) * (-Y) + (Y + y) / (2 * Y) * Y = (2 * Y * y) / (2 * Y) := by ring
    rw [e, mul_div_assoc, mul_comm, div_mul_cancel₀ _ h2Y] 
  simp only [smul_eq_mul] at h
  rwa [hy] at h

/-- LDLᵀ: with `a = m11 > 0`, `m = m11 m22 - m12² > 0` and `Δ = det > 0`,
`a m (xᵀ M x) = m (a x1 + m12 x2 + m01 x0)² + (m x2 + (a m02 - m12 m01) x0)² + a Δ x0²`. -/
theorem quad3_nonneg_of_minors {m00 m01 m02 m11 m12 m22 : ℝ} (ha : 0 < m11)
    (hm : 0 < m11 * m22 - m12 ^ 2)
    (hdet : 0 < m00 * (m11 * m22 - m12 ^ 2) - m01 * (m01 * m22 - m12 * m02)
      + m02 * (m01 * m12 - m11 * m02)) (x : Fin 3 → ℝ) :
    0 ≤ quad3 m00 m01 m02 m11 m12 m22 x := by
  set m := m11 * m22 - m12 ^ 2
  have key : m11 * m * quad3 m00 m01 m02 m11 m12 m22 x =
      m * (m11 * x 1 + m12 * x 2 + m01 * x 0) ^ 2
        + (m * x 2 + (m11 * m02 - m12 * m01) * x 0) ^ 2
        + m11 * (m00 * (m11 * m22 - m12 ^ 2) - m01 * (m01 * m22 - m12 * m02)
            + m02 * (m01 * m12 - m11 * m02)) * x 0 ^ 2 := by
    simp only [quad3, m]; ring
  have hr : 0 ≤ m11 * m * quad3 m00 m01 m02 m11 m12 m22 x := by
    rw [key]; positivity
  exact (mul_nonneg_iff_of_pos_left (mul_pos ha hm)).1 hr

end OM.NNN18
