import Lib.OM.NNN30.Net.Support

/-! # Supporting prices at an arbitrary positive format -/

noncomputable section
namespace OM.NNN36

open NNN22 NNN24.Mm NNN30.Net

/-- On the box from zero to `w`, the largest ratio `xᵢ / wᵢ` bounds
`F(x) / F(w)` by monotonicity and homogeneity. Minimax supplies one mixture
of the three coordinate bounds that supports the entire orthant. -/
theorem supporting_price_at (φ : PolMul.Spectral ℂ) (w : Fin 3 → ℝ) (hw : ∀ i, 0 < w i) :
    ∃ h : Fin 3 → ℝ, (∀ i, 0 ≤ h i) ∧ (∑ i, h i * w i) = Fv φ w ∧
      ∀ y : Fin 3 → ℝ, (∀ i, 0 ≤ y i) → Fv φ y ≤ ∑ i, h i * y i := by
  classical
  let g := Fv φ w
  let box := Set.Icc (0 : Fin 3 → ℝ) w
  let L := fun (x p : Fin 3 → ℝ) => ∑ i, (g * p i / w i) * x i
  let f := fun x p => L x p - Fv φ x
  have horth : box ⊆ orth := fun _ hx => hx.1
  have hcontX (p) : Continuous (L · p) := by dsimp [L]; fun_prop
  have hcontP (x) : Continuous (L x) := by dsimp [L]; fun_prop
  have hconv (p) : ConvexOn ℝ box (L · p) := by
    refine ⟨convex_Icc _ _, fun x _ y _ a b _ _ _ => ?_⟩
    simp only [L, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact (Finset.sum_congr rfl fun i _ => by ring).le
  have hconc (x) : ConcaveOn ℝ (Simp 3) (f x) := by
    refine ⟨convex_Simp _, fun p _ q _ a b _ _ hab => ?_⟩
    have hadd : L x (a • p + b • q) = a * L x p + b * L x q := by
      simp only [L, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    simp only [f, smul_eq_mul, hadd]
    linear_combination -(Fv φ x) * hab
  have hFc : ConcaveOn ℝ box (Fv φ) := (Fv_concaveOn φ).subset horth (convex_Icc _ _)
  have hF : ContinuousOn (Fv φ) box := (Fv_continuousOn φ).mono horth
  let e := fun (j i : Fin 3) => if i = j then (1 : ℝ) else 0
  have he (j) : e j ∈ Simp 3 := ⟨fun i => by dsimp [e]; positivity, by simp [e]⟩
  obtain ⟨a, ha, p, hp, saddle⟩ := Sion.exists_isSaddlePointOn (f := f)
    (show box.Nonempty from ⟨0, le_rfl, fun i => (hw i).le⟩) (convex_Icc _ _) isCompact_Icc
    (fun q _ => ((hcontX q).continuousOn.sub hF).lowerSemicontinuousOn)
    (fun q _ => ((hconv q).sub hFc).quasiconvexOn)
    (convex_Simp _) ⟨_, he 0⟩ (isCompact_Simp _)
    (fun x _ => ((hcontP x).sub continuous_const).continuousOn.upperSemicontinuousOn)
    (fun x _ => (hconc x).quasiconcaveOn)
  obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ (fun i => a i / w i) Finset.univ_nonempty
  have hM := Fv_mono φ (y := a) (y' := fun i => (a j / w j) * w i)
    (fun i => (div_le_iff₀ (hw i)).mp (hj i (Finset.mem_univ i)))
  have hs := Fv_smul φ (y := w) (fun i => (hw i).le) (div_nonneg (ha.1 j) (hw j).le)
  have hpos : 0 ≤ f a (e j) := by
    have hL : L a (e j) = g / w j * a j := by simp [L, e, mul_ite, ite_div, ite_mul]
    dsimp only [f]
    rw [hL, sub_nonneg]
    exact hM.trans_eq (hs.trans (by dsimp only [g]; ring))
  have hbox (x) (hx : x ∈ box) : Fv φ x ≤ L x p := sub_nonneg.mp (hpos.trans (saddle x hx _ (he j)))
  refine ⟨fun i => g * p i / w i,
    fun i => div_nonneg (mul_nonneg (Fv_nonneg φ _) (hp.1 i)) (hw i).le, ?_, ?_⟩
  · simp only [div_mul_cancel₀ _ (hw _).ne', ← Finset.mul_sum, hp.2, mul_one, g]
  intro y hy
  let r := 1 + ∑ i, y i / w i
  have hr : 0 < r := add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg fun i _ => div_nonneg (hy i) (hw i).le)
  let x := fun i => y i / r
  have hx : x ∈ box := ⟨fun i => div_nonneg (hy i) hr.le, fun i => by
    have hr' : y i / w i ≤ r := by
      have h := Finset.single_le_sum (f := fun i => y i / w i)
        (fun j _ => div_nonneg (hy j) (hw j).le) (Finset.mem_univ i)
      dsimp only [r]; linarith
    exact (div_le_iff₀ hr).2 (((div_le_iff₀ (hw i)).mp hr').trans_eq (mul_comm _ _))⟩
  have heq (i) : r * x i = y i := by dsimp only [x]; field_simp
  calc
    Fv φ y = r * Fv φ x := by simpa only [heq] using Fv_smul φ (y := x) hx.1 hr.le
    _ ≤ r * L x p := mul_le_mul_of_nonneg_left (hbox x hx) hr.le
    _ = _ := by
      dsimp only [L]; rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [mul_left_comm, heq]

end OM.NNN36

