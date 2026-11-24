import Lib.OM.NNN36.WeightedAngle
import Lib.OM.NNN36.PriceSpace
import Mathlib.Analysis.InnerProductSpace.Basic

/-! # The weighted spectral estimate on a Euclidean triangle -/

noncomputable section
namespace OM.NNN36

open scoped InnerProductSpace
open NNN22 NNN30.Geom Foundations.PairUnitExponents

private theorem comparison_edge {f g : ℂ} {u v w a b D : ℝ}
    (hu : 0 < u) (hv : 0 < v) (ha : 0 ≤ a) (hb : 0 ≤ b) (hD : 0 ≤ D)
    (hf : ‖f‖ = u) (hg : ‖g‖ = v) (hsum : ‖f+g‖ = w)
    (hangle : (a^2+b^2-D^2)*(u*v) ≤ a*b*(w^2-u^2-v^2)) :
    ‖(a/u) • f - (b/v) • g‖ ≤ D := by
  have hinner := norm_add_sq_real f g
  rw [hsum,hf,hg] at hinner
  have hd : 2 * ⟪(a/u) • f, (b/v) • g⟫_ℝ = a*b*(w^2-u^2-v^2)/(u*v) := by
    rw [real_inner_smul_left, real_inner_smul_right,
      show w^2-u^2-v^2 = 2*⟪f,g⟫_ℝ by linarith only [hinner]]
    ring
  have hn {x : ℂ} {s t : ℝ} (hs : 0 ≤ s) (ht : 0 < t) (hx : ‖x‖ = t) :
      ‖(s/t) • x‖ = s := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hs ht.le), hx, div_mul_cancel₀ _ ht.ne']
  apply (sq_le_sq₀ (norm_nonneg _) hD).mp
  rw [norm_sub_sq_real, hd, hn ha hu hf, hn hb hv hg]
  linarith only [(le_div_iff₀ (mul_pos hu hv)).mpr hangle]

private theorem side_work (f : ℂ) {s : ℝ} (hs : 0 < s) (hf : ‖f‖ = s) (h : ℝ) :
    ⟪f, (h/s) • f⟫_ℝ = s*h := by
  rw [real_inner_smul_right, real_inner_self_eq_norm_sq, hf]
  field_simp

/-- Vertex `qᵢ` contributes the distance to it times the price between the other
two terminals. The point `z` may lie anywhere in the plane. -/
theorem triangle_price (crossing : S_R108_3) (φ : PolMul.Spectral ℂ)
    (q₁ q₂ q₃ z : ℂ) {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h₁ : ‖q₂-q₃‖ = a) (h₂ : ‖q₃-q₁‖ = b) (h₃ : ‖q₁-q₂‖ = c) :
    Fv φ ![a,b,c] ≤ dist z q₁ * theta φ 0 + dist z q₂ * theta φ 1 + dist z q₃ * theta φ 2 := by
  obtain ⟨S,o,p,lo,hi,t₁,t₂,t₃⟩ := weighted_price_space crossing φ ![a,b,c]
    (fun i => by fin_cases i <;> first | exact ha | exact hb | exact hc)
  let h := fun i => S.d o (p i)
  have hmin (x) : a*h 0 + b*h 1 + c*h 2 ≤ a*S.d x (p 0) + b*S.d x (p 1) + c*S.d x (p 2) := by
    simpa [Fin.sum_univ_three, h] using hi.trans (lo x)
  let V₁ := (h 0/a) • (q₂-q₃)
  let V₂ := (h 1/b) • (q₃-q₁)
  let V₃ := (h 2/c) • (q₁-q₂)
  have sides (x y t : ℂ) : ‖(x-y)+(y-t)‖ = ‖t-x‖ := by
    rw [show x-y+(y-t) = -(t-x) by abel, norm_neg]
  have e₁ : ‖V₂-V₃‖ ≤ theta φ 0 :=
    (comparison_edge hb hc (S.d_nonneg _ _) (S.d_nonneg _ _) (S.d_nonneg _ _) h₂ h₃
      ((sides ..).trans h₁) (weighted_angle S o (p 1) (p 2) (p 0) hb hc ha.le
        (fun x => by linarith only [hmin x]))).trans t₁
  have e₂ : ‖V₃-V₁‖ ≤ theta φ 1 :=
    (comparison_edge hc ha (S.d_nonneg _ _) (S.d_nonneg _ _) (S.d_nonneg _ _) h₃ h₁
      ((sides ..).trans h₂) (weighted_angle S o (p 2) (p 0) (p 1) hc ha hb.le
        (fun x => by linarith only [hmin x]))).trans t₂
  have e₃ : ‖V₁-V₂‖ ≤ theta φ 2 :=
    (comparison_edge ha hb (S.d_nonneg _ _) (S.d_nonneg _ _) (S.d_nonneg _ _) h₁ h₂
      ((sides ..).trans h₃) (weighted_angle S o (p 0) (p 1) (p 2) ha hb hc.le hmin)).trans t₃
  have term (q v v' : ℂ) {t : ℝ} (ht : ‖v-v'‖ ≤ t) :
      ⟪q-z,v'-v⟫_ℝ ≤ dist z q * t := by
    rw [dist_comm, dist_eq_norm]
    apply (real_inner_le_norm _ _).trans
    exact mul_le_mul_of_nonneg_left ((norm_sub_rev v' v).le.trans ht) (norm_nonneg _)
  calc
    Fv φ ![a,b,c] ≤ a*h 0 + b*h 1 + c*h 2 := by
      simpa [Fin.sum_univ_three,h] using lo o
    _ = ⟪q₂-q₃,V₁⟫_ℝ + ⟪q₃-q₁,V₂⟫_ℝ + ⟪q₁-q₂,V₃⟫_ℝ := by
      rw [side_work _ ha h₁,side_work _ hb h₂,side_work _ hc h₃]
    _ = ⟪q₁-z,V₃-V₂⟫_ℝ + ⟪q₂-z,V₁-V₃⟫_ℝ + ⟪q₃-z,V₂-V₁⟫_ℝ := by
      simp only [inner_sub_left,inner_sub_right]; ring
    _ ≤ _ := add_le_add (add_le_add (term _ _ _ e₁) (term _ _ _ e₂)) (term _ _ _ e₃)

end OM.NNN36

