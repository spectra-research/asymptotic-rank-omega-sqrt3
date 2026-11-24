import Lib.OM.NNN18.PackedCore

/-!
`f y = ratPart a b ρ₁ 0 h k y + ratPart 0 0 ρ₂ 0 h (-k) y - K (y - H)_+²`.  Its derivative is
antitone on `[l, H]` and on `[H, u]` when the smooth curvature
`g y = 2k²(ρ₁/(h+ky)³ + ρ₂/(h-ky)³)` is `≤ 0` below the hinge and `≤ 2K` above it.
-/

noncomputable section
open Set
namespace OM.NNN18

/-- The derivative of the hinge-corrected entry. -/
def hingeDeriv (b ρ₁ ρ₂ h k K H y : ℝ) : ℝ :=
  b - ρ₁ * k / (h + k * y) ^ 2 + ρ₂ * k / (h - k * y) ^ 2 - K * (2 * max (y - H) 0)

lemma hasDerivAt_hingeEntry (a b ρ₁ ρ₂ h k K H y : ℝ) (h1 : h + k * y ≠ 0)
    (h2 : h - k * y ≠ 0) :
    HasDerivAt (fun y => ratPart a b ρ₁ 0 h k y + ratPart 0 0 ρ₂ 0 h (-k) y - K * hinge H y)
      (hingeDeriv b ρ₁ ρ₂ h k K H y) y := by
  have e2 : h + -k * y = h - k * y := by ring
  have d1 := hasDerivAt_ratPart a b ρ₁ 0 h k y h1
  have d2 := hasDerivAt_ratPart 0 0 ρ₂ 0 h (-k) y (by rw [e2]; exact h2)
  have d3 := (hasDerivAt_hinge H y).const_mul K
  convert! (d1.add d2).sub d3 using 1
  simp only [hingeDeriv, e2]
  ring

/-- The smooth curvature of the hinge entry. -/
def hingeCurv (ρ₁ ρ₂ h k y : ℝ) : ℝ := 2 * k ^ 2 * (ρ₁ / (h + k * y) ^ 3 + ρ₂ / (h - k * y) ^ 3)

lemma hasDerivAt_hingeDeriv_below (b ρ₁ ρ₂ h k K H y : ℝ) (h1 : h + k * y ≠ 0)
    (h2 : h - k * y ≠ 0) (hy : y < H) :
    HasDerivAt (hingeDeriv b ρ₁ ρ₂ h k K H) (hingeCurv ρ₁ ρ₂ h k y) y := by
  have e2 : h + -k * y = h - k * y := by ring
  have d1 := hasDerivAt_ratPart' b ρ₁ 0 h k y h1
  have d2 := hasDerivAt_ratPart' 0 ρ₂ 0 h (-k) y (by rw [e2]; exact h2)
  have hev : (hingeDeriv b ρ₁ ρ₂ h k K H) =ᶠ[nhds y]
      fun w => (b - ρ₁ * k / (h + k * w) ^ 2 - 2 * 0 * k / (h + k * w) ^ 3)
        + (0 - ρ₂ * (-k) / (h + -k * w) ^ 2 - 2 * 0 * (-k) / (h + -k * w) ^ 3) := by
    filter_upwards [Iio_mem_nhds hy] with w hw
    have hw' : w - H ≤ 0 := by linarith [Set.mem_Iio.1 hw]
    simp only [hingeDeriv, max_eq_right hw']
    have : h + -k * w = h - k * w := by ring
    rw [this]; ring
  refine ((d1.add d2).congr_deriv ?_).congr_of_eventuallyEq hev
  simp only [hingeCurv, e2]
  field_simp
  ring

lemma hasDerivAt_hingeDeriv_above (b ρ₁ ρ₂ h k K H y : ℝ) (h1 : h + k * y ≠ 0)
    (h2 : h - k * y ≠ 0) (hy : H < y) :
    HasDerivAt (hingeDeriv b ρ₁ ρ₂ h k K H) (hingeCurv ρ₁ ρ₂ h k y - 2 * K) y := by
  have e2 : h + -k * y = h - k * y := by ring
  have d1 := hasDerivAt_ratPart' b ρ₁ 0 h k y h1
  have d2 := hasDerivAt_ratPart' 0 ρ₂ 0 h (-k) y (by rw [e2]; exact h2)
  have d3 : HasDerivAt (fun w => K * (2 * (w - H))) (2 * K) y := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_id y).sub_const H).const_mul 2).const_mul K
  have hev : (hingeDeriv b ρ₁ ρ₂ h k K H) =ᶠ[nhds y]
      fun w => (b - ρ₁ * k / (h + k * w) ^ 2 - 2 * 0 * k / (h + k * w) ^ 3)
        + (0 - ρ₂ * (-k) / (h + -k * w) ^ 2 - 2 * 0 * (-k) / (h + -k * w) ^ 3)
        - K * (2 * (w - H)) := by
    filter_upwards [Ioi_mem_nhds hy] with w hw
    have hw' : 0 ≤ w - H := by linarith [Set.mem_Ioi.1 hw]
    simp only [hingeDeriv, max_eq_left hw']
    have : h + -k * w = h - k * w := by ring
    rw [this]; ring
  refine (((d1.add d2).sub d3).congr_deriv ?_).congr_of_eventuallyEq hev
  simp only [hingeCurv, e2]
  field_simp
  ring

lemma continuousOn_hingeDeriv {b ρ₁ ρ₂ h k K H l u : ℝ}
    (hpos : ∀ y ∈ Icc l u, 0 < h + k * y ∧ 0 < h - k * y) :
    ContinuousOn (hingeDeriv b ρ₁ ρ₂ h k K H) (Icc l u) := by
  intro y hy
  obtain ⟨p1, p2⟩ := hpos y hy
  unfold hingeDeriv
  apply ContinuousAt.continuousWithinAt
  have c1 : ContinuousAt (fun w => h + k * w) y := by fun_prop
  have c2 : ContinuousAt (fun w => h - k * w) y := by fun_prop
  apply ContinuousAt.sub
  · apply ContinuousAt.add
    · apply ContinuousAt.sub continuousAt_const
      exact continuousAt_const.div (c1.pow 2) (pow_ne_zero 2 p1.ne')
    · exact continuousAt_const.div (c2.pow 2) (pow_ne_zero 2 p2.ne')
  · exact continuousAt_const.mul (continuousAt_const.mul
      ((continuous_id.sub continuous_const).max continuous_const).continuousAt)

/-- **Concavity of the hinge entry.** -/
theorem concaveOn_hingeEntry {a b ρ₁ ρ₂ h k K H l u : ℝ}
    (hpos : ∀ y ∈ Icc l u, 0 < h + k * y ∧ 0 < h - k * y)
    (hneg : ∀ y ∈ Icc l u, y ≤ H → hingeCurv ρ₁ ρ₂ h k y ≤ 0)
    (hup : ∀ y ∈ Icc l u, H ≤ y → hingeCurv ρ₁ ρ₂ h k y ≤ 2 * K) :
    ConcaveOn ℝ (Icc l u) (fun y => ratPart a b ρ₁ 0 h k y + ratPart 0 0 ρ₂ 0 h (-k) y
      - K * hinge H y) := by
  have hd : ∀ y ∈ Icc l u, HasDerivAt
      (fun y => ratPart a b ρ₁ 0 h k y + ratPart 0 0 ρ₂ 0 h (-k) y - K * hinge H y)
      (hingeDeriv b ρ₁ ρ₂ h k K H y) y := fun y hy =>
    hasDerivAt_hingeEntry a b ρ₁ ρ₂ h k K H y (hpos y hy).1.ne' (hpos y hy).2.ne'
  have hcont := continuousOn_hingeDeriv (b := b) (ρ₁ := ρ₁) (ρ₂ := ρ₂) (K := K) (H := H) hpos
  -- antitone derivative
  have hanti : AntitoneOn (hingeDeriv b ρ₁ ρ₂ h k K H) (Icc l u) := by
    have below : ∀ m, m ≤ H → l ≤ m → m ≤ u →
        AntitoneOn (hingeDeriv b ρ₁ ρ₂ h k K H) (Icc l m) := by
      intro m hmH hlm hmu
      apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc l m)
        (hcont.mono (Icc_subset_Icc le_rfl hmu)) (f' := hingeCurv ρ₁ ρ₂ h k)
      · intro y hy
        rw [interior_Icc] at hy
        have hyI : y ∈ Icc l u := ⟨hy.1.le, hy.2.le.trans hmu⟩
        exact (hasDerivAt_hingeDeriv_below b ρ₁ ρ₂ h k K H y (hpos y hyI).1.ne'
          (hpos y hyI).2.ne' (hy.2.trans_le hmH)).hasDerivWithinAt
      · intro y hy
        rw [interior_Icc] at hy
        exact hneg y ⟨hy.1.le, hy.2.le.trans hmu⟩ (hy.2.le.trans hmH)
    have above : ∀ m, H ≤ m → l ≤ m → m ≤ u →
        AntitoneOn (hingeDeriv b ρ₁ ρ₂ h k K H) (Icc m u) := by
      intro m hHm hlm hmu
      apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc m u)
        (hcont.mono (Icc_subset_Icc hlm le_rfl)) (f' := fun y => hingeCurv ρ₁ ρ₂ h k y - 2 * K)
      · intro y hy
        rw [interior_Icc] at hy
        have hyI : y ∈ Icc l u := ⟨hlm.trans hy.1.le, hy.2.le⟩
        exact (hasDerivAt_hingeDeriv_above b ρ₁ ρ₂ h k K H y (hpos y hyI).1.ne'
          (hpos y hyI).2.ne' (hHm.trans_lt hy.1)).hasDerivWithinAt
      · intro y hy
        rw [interior_Icc] at hy
        have := hup y ⟨hlm.trans hy.1.le, hy.2.le⟩ (hHm.trans hy.1.le)
        linarith
    rcases le_or_gt u l with hul | hlu
    · intro x hx y hy _
      have : x = y := by linarith [hx.1, hx.2, hy.1, hy.2]
      rw [this]
    · by_cases hHu : u ≤ H
      · exact below u hHu hlu.le le_rfl
      · push_neg at hHu
        by_cases hlH : H ≤ l
        · exact above l hlH le_rfl hlu.le
        · push_neg at hlH
          exact antitoneOn_glue (below H le_rfl hlH.le hHu.le) (above H le_rfl hlH.le hHu.le)
            hlH.le hHu.le
  have hderiv : ∀ y ∈ interior (Icc l u), deriv
      (fun y => ratPart a b ρ₁ 0 h k y + ratPart 0 0 ρ₂ 0 h (-k) y - K * hinge H y) y =
      hingeDeriv b ρ₁ ρ₂ h k K H y := fun y hy => (hd y (interior_subset hy)).deriv
  apply AntitoneOn.concaveOn_of_deriv (convex_Icc l u)
  · exact fun y hy => (hd y hy).continuousAt.continuousWithinAt
  · exact fun y hy => (hd y (interior_subset hy)).differentiableAt.differentiableWithinAt
  · intro x hx y hy hxy
    rw [hderiv x hx, hderiv y hy]
    exact hanti (interior_subset hx) (interior_subset hy) hxy

end OM.NNN18
