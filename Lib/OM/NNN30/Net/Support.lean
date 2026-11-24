import Lib.OM.NNN30.Net.Sandwich
import Lib.OM.NNN24.FCont

/-! # A supporting price vector for the cube format

Put `g = F(1,1,1)`. For every nonnegative format `y`, monotonicity and homogeneity give
`F(y) ≤ g maxᵢ yᵢ`. On the unit box the right hand side is the maximum of
`g ∑ᵢ pᵢ yᵢ` over probability vectors. Sion gives one probability vector for the whole box.
Homogeneity extends its bound to the orthant. -/

noncomputable section
open scoped BigOperators

namespace OM.NNN30.Net

open OM.NNN22 OM.NNN24.Mm

theorem supporting_prices (φ : OM.PolMul.Spectral ℂ) :
    ∃ h : Fin 3 → ℝ, (∀ i, 0 ≤ h i) ∧ (∑ i, h i) = P2M.R88.Fv φ (fun _ => 1) ∧
      ∀ y : Fin 3 → ℝ, (∀ i, 0 ≤ y i) → Fv φ y ≤ ∑ i, h i * y i := by
  classical
  let g := Fv φ (fun _ => 1)
  have hg : 0 ≤ g := Fv_nonneg φ _
  let box := Set.Icc (0 : Fin 3 → ℝ) 1
  let L := fun (x p : Fin 3 → ℝ) => ∑ i, (g * p i) * x i
  let f := fun x p => L x p - Fv φ x
  have horth : box ⊆ orth := fun _ hx => hx.1
  have hxcont (p : Fin 3 → ℝ) : Continuous (fun x => L x p) := by dsimp [L]; fun_prop
  have hpcont (x : Fin 3 → ℝ) : Continuous (fun p => L x p) := by dsimp [L]; fun_prop
  have hxc (p : Fin 3 → ℝ) : ConvexOn ℝ box (fun x => L x p) := by
    refine ⟨convex_Icc _ _, fun x _ y _ a b _ _ _ => ?_⟩
    simp only [L, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact le_of_eq (Finset.sum_congr rfl fun i _ => by ring)
  have hpc (x : Fin 3 → ℝ) : ConcaveOn ℝ (Simp 3) (fun p => f x p) := by
    refine ⟨convex_Simp _, fun p _ q _ a b _ _ hab => ?_⟩
    have hL : L x (a • p + b • q) = a * L x p + b * L x q := by
      simp only [L, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    simp only [f, smul_eq_mul, hL]
    linear_combination -(Fv φ x) * hab
  have hcF : ConcaveOn ℝ box (Fv φ) := (Fv_concaveOn φ).subset horth (convex_Icc _ _)
  have hF : ContinuousOn (Fv φ) box := (Fv_continuousOn φ).mono horth
  let e := fun (j i : Fin 3) => if i = j then (1 : ℝ) else 0
  have he (j) : e j ∈ Simp 3 := ⟨fun i => by dsimp [e]; positivity, by simp [e]⟩
  obtain ⟨a, ha, p, hp, hs⟩ := Sion.exists_isSaddlePointOn (f := f)
    (show box.Nonempty from ⟨0, le_rfl, by intro i; norm_num⟩)
    (convex_Icc _ _) isCompact_Icc
    (fun q _ => ((hxcont q).continuousOn.sub hF).lowerSemicontinuousOn)
    (fun q _ => ((hxc q).sub hcF).quasiconvexOn)
    (convex_Simp _) ⟨_, he 0⟩ (isCompact_Simp _)
    (fun x _ => ((hpcont x).sub continuous_const).continuousOn.upperSemicontinuousOn)
    (fun x _ => (hpc x).quasiconcaveOn)
  obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ a Finset.univ_nonempty
  have hm := Fv_mono φ (y := a) (y' := fun _ => a j) (fun i => hj i (Finset.mem_univ i))
  have hscl := Fv_smul φ (y := fun _ : Fin 3 => (1 : ℝ)) (fun _ => zero_le_one) (ha.1 j)
  simp only [mul_one] at hscl
  have hj0 : 0 ≤ f a (e j) := by
    have hdot : L a (e j) = g * a j := by
      simp [L, e, mul_ite, ite_mul]
    dsimp only [f]
    rw [hdot]
    change Fv φ (fun _ => a j) = a j * g at hscl
    linarith only [hm, hscl, mul_comm g (a j)]
  have hbox (x) (hx : x ∈ box) : Fv φ x ≤ L x p := by
    have hi := hj0.trans (hs x hx _ (he j))
    exact sub_nonneg.mp hi
  refine ⟨fun i => g * p i, fun i => mul_nonneg hg (hp.1 i), ?_, ?_⟩
  · rw [← Finset.mul_sum, hp.2, mul_one]
    rfl
  intro y hy
  let r := 1 + ∑ i, y i
  have hr : 0 < r := add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg fun i _ => hy i)
  let x := fun i => y i / r
  have hx : x ∈ box := ⟨fun i => div_nonneg (hy i) hr.le, fun i => by
    apply (div_le_one hr).2
    have hle := Finset.single_le_sum (fun i _ => hy i) (Finset.mem_univ i)
    dsimp [r]; linarith⟩
  have heq (i) : r * x i = y i := by dsimp [x]; field_simp
  calc
    Fv φ y = r * Fv φ x := by
      have h := Fv_smul φ (y := x) hx.1 hr.le
      simpa only [heq] using h
    _ ≤ r * L x p := mul_le_mul_of_nonneg_left (hbox x hx) hr.le
    _ = _ := by
      rw [show L x p = ∑ i, (g * p i) * x i from rfl, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [mul_left_comm, heq]

end OM.NNN30.Net
