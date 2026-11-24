import PLATFORM.Statements.«R115.2»
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-! # Coordinates of the log-dimension triangle and its cubic test -/

namespace OM.NNN36

open P2M.R115

theorem apex_geometry {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c) (ht : c < a+b) :
    let q := normalizedApex a b c
    (1/2 ≤ q.re ∧ q.re < 1) ∧ 0 < q.im ∧ ‖(c : ℂ) - c*q‖ = a ∧ ‖(c : ℂ)*q‖ = b := by
  let q := normalizedApex a b c
  have hb := ha.trans_le hab
  have hc := hb.trans_le hbc
  have hx : 2*c^2*q.re = b^2+c^2-a^2 := by
    change 2*c^2*((b^2+c^2-a^2)/(2*c^2)) = _
    field_simp
  have harea : (b/c)^2-q.re^2 =
      (a+b+c)*(a+b-c)*(a+c-b)*(b+c-a)/(4*c^4) := by
    change (b/c)^2-((b^2+c^2-a^2)/(2*c^2))^2 = _
    field_simp; ring
  have hpos : 0 < (b/c)^2-q.re^2 := by
    rw [harea]
    have : 0 < a+b-c := by linarith
    have : 0 < a+c-b := by linarith
    have : 0 < b+c-a := by linarith
    positivity
  have hy : q.im^2 = (b/c)^2-q.re^2 := Real.sq_sqrt hpos.le
  have hsq : c^2 * (q.re^2 + q.im^2) = b^2 := by rw [hy]; field_simp; ring
  have hhalf : 1/2 ≤ q.re := by
    apply (le_of_mul_le_mul_left (a := 2*c^2) (by nlinarith only [hx, pow_le_pow_left₀ ha.le hab 2]) (by positivity))
  have hlt : q.re < 1 := by
    apply (lt_of_mul_lt_mul_left (a := 2*c^2) (by nlinarith only [hx, pow_le_pow_left₀ hb.le hbc 2, sq_pos_of_pos ha]) (by positivity))
  refine ⟨⟨hhalf,hlt⟩, Real.sqrt_pos.mpr hpos, ?_, ?_⟩
  · apply (sq_eq_sq₀ (norm_nonneg _) ha.le).mp
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, sub_zero, zero_sub]
    linear_combination hsq - hx
  · apply (sq_eq_sq₀ (norm_nonneg _) hb.le).mp
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero, sub_zero]
    linear_combination hsq

private abbrev cubic (x : ℝ) := 3*x^2-2*x^3

private theorem cubic_strictMono : StrictMonoOn cubic (Set.Icc 0 1) := by
  intro x hx y hy hxy
  have hfactor : 0 < 2*x*(1-x) + 2*y*(1-y) + x*(1-y) + y*(1-x) := by
    have hx0 := hx.1
    have hy0 := hx0.trans_lt hxy
    have hx1 := sub_pos.mpr (hxy.trans_le hy.2)
    have hy1 := sub_nonneg.mpr hy.2
    positivity
  exact sub_pos.mp ((mul_pos (sub_pos.mpr hxy) hfactor).trans_eq (by dsimp [cubic]; ring))

theorem cubic_root {ξ : ℝ} (hξ : ξ ∈ Set.Ioo 0 1) :
    ∃! x, x ∈ Set.Ioo 0 1 ∧ 3*x^2-2*x^3 = ξ := by
  have hf : Continuous cubic := by unfold cubic; fun_prop
  obtain ⟨x,hx,he⟩ := intermediate_value_Icc (zero_le_one' ℝ) hf.continuousOn
    (show ξ ∈ Set.Icc (cubic 0) (cubic 1) by norm_num [cubic]; exact ⟨hξ.1.le,hξ.2.le⟩)
  have hx₀ : 0 ≠ x := fun e => hξ.1.ne (by simpa [← e,cubic] using he)
  have hx₁ : x ≠ 1 := by
    intro e
    exact hξ.2.ne (he.symm.trans (by rw [e]; norm_num [cubic]))
  refine ⟨x,⟨⟨hx.1.lt_of_ne hx₀,hx.2.lt_of_ne hx₁⟩,he⟩,?_⟩
  exact fun y ⟨hy,hy'⟩ => cubic_strictMono.injOn ⟨hy.1.le,hy.2.le⟩ hx (hy'.trans he.symm)

theorem half_le_of_cubic {x ξ : ℝ} (hx : x ∈ Set.Ioo 0 1) (he : 3*x^2-2*x^3 = ξ)
    (hξ : 1/2 ≤ ξ) : 1/2 ≤ x := by
  by_contra! h
  have hl := cubic_strictMono ⟨hx.1.le,hx.2.le⟩ (show 1/2 ∈ Set.Icc (0 : ℝ) 1 by constructor <;> norm_num) h
  norm_num [cubic] at hl
  linarith

end OM.NNN36
