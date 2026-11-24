import Lib.OM.Formats.PlaneBill

/-! # First variation of the two planar network costs -/

noncomputable section
open scoped InnerProductSpace
namespace OM.Formats

open NNN34 Filter Topology

private lemma shifted_distance {e : ℂ} (he : ‖e‖ = 1) {k : ℝ} (hk : 1 ≤ k)
    (z : ℂ) {s : ℝ} (hs : 0 ≤ s) :
    dist (k • e) (s • z) ≤ k - s*⟪e,z⟫_ℝ + s^2*‖z‖^2 := by
  rw [dist_eq_norm]
  have sq := norm_sub_sq_real (k • e) (s • z)
  rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (by linarith),abs_of_nonneg hs,
    real_inner_smul_left,real_inner_smul_right,he,mul_one] at sq
  by_contra! bad
  nlinarith only [mul_lt_mul_of_pos_left bad (show 0 < 2*k by linarith),
    sq_nonneg (‖k • e-s • z‖ - k),sq,
    mul_nonneg (show 0 ≤ 2*k-1 by linarith) (mul_nonneg (sq_nonneg s) (sq_nonneg ‖z‖))]

private lemma two_rays {X Y : ℂ} (hX : ‖X‖ = 1) (hY : ‖Y‖ = 2) :
    Function.Injective (![X,Y,-Y,-X] : Fin 4 → ℂ) := by
  have opp (z : ℂ) (hz : 0 < ‖z‖) : z ≠ -z := by
    intro h
    apply norm_pos_iff.mp hz
    linear_combination h/2
  have x := opp X (by linarith)
  have y := opp Y (by linarith)
  intro i j he
  fin_cases i <;> fin_cases j <;> first
    | rfl
    | exact (x he).elim
    | exact (x he.symm).elim
    | exact (y he).elim
    | exact (y he.symm).elim
    | have hn := congrArg norm he; norm_num [hX,hY] at hn

private lemma first_variation {v w β κ : ℝ} (hv : 0 ≤ v) (hw : 0 ≤ w)
    {X Y : ℂ} (hX : ‖X‖ = 1) (hY : ‖Y‖ = 1) (l r h : ℂ)
    (prices : ∀ (s : ℝ), 0 < s → bill dist ![X,(2:ℝ) • Y,-((2:ℝ) • Y),-X] v w β κ
      (s • l) (s • r) 0 (s • h) 0) :
    v*⟪X,l⟫_ℝ + w*⟪Y,r⟫_ℝ ≤ β/2*perimeter3 dist l r 0 ∨
    v*⟪X,h⟫_ℝ - w*⟪Y,h⟫_ℝ ≤ κ*‖h‖ := by
  let W := (2:ℝ) • Y
  have hW : ‖W‖ = 2 := by simp [W,hY]
  have diam (z : ℂ) : dist z (-z) = 2*‖z‖ := by
    rw [dist_eq_norm,sub_neg_eq_add,← two_smul ℝ z,norm_smul]; norm_num
  let R := β/2*perimeter3 dist l r 0 - (v*⟪X,l⟫_ℝ + w*⟪Y,r⟫_ℝ)
  let C := κ*‖h‖ - (v*⟪X,h⟫_ℝ - w*⟪Y,h⟫_ℝ)
  let M := v*‖l‖^2 + w*‖r‖^2
  let N := v*‖h‖^2 + w*‖h‖^2
  have approx (s : ℝ) (hs : 0 < s) : 0 ≤ max (R+s*M) (C+s*N) := by
    have H := prices s hs
    change v*dist X (-X) + w*dist W (-W) ≤
      max (v*dist X (s • l) + w*dist W (s • r) + w*dist (-W) 0 + v*dist (-X) 0 +
        β/2*perimeter3 dist (s • l) (s • r) 0)
        (v*dist X (s • h) + w*dist W 0 + w*dist (-W) (s • h) + v*dist (-X) 0 + κ*dist (s • h) 0) at H
    have per : perimeter3 dist (s • l) (s • r) 0 = s*perimeter3 dist l r 0 := by
      unfold perimeter3
      rw [dist_smul₀,dist_zero_right,dist_zero_left,dist_zero_right,dist_zero_left,norm_smul,norm_smul,
        Real.norm_eq_abs,abs_of_pos hs]
      ring
    simp only [diam,dist_zero_right,hW,hX,norm_neg,per,norm_smul,Real.norm_eq_abs,abs_of_pos hs] at H
    have boundX (z : ℂ) : dist X (s • z) ≤ 1-s*⟪X,z⟫_ℝ+s^2*‖z‖^2 := by
      simpa using shifted_distance hX (le_refl (1:ℝ)) z hs.le
    have boundW (z : ℂ) : dist W (s • z) ≤ 2-s*⟪Y,z⟫_ℝ+s^2*‖z‖^2 :=
      shifted_distance hY one_le_two z hs.le
    have negW : dist (-W) (s • h) ≤ 2+s*⟪Y,h⟫_ℝ+s^2*‖h‖^2 := by
      simpa only [W,smul_neg,inner_neg_left,mul_neg,sub_neg_eq_add] using shifted_distance (e := -Y) (by simpa using hY) one_le_two h hs.le
    rcases le_max_iff.mp H with H | H
    · apply (le_max_left (R+s*M) _).trans'
      apply nonneg_of_mul_nonneg_right (a := s) _ hs
      dsimp only [R,M]
      nlinarith only [H,mul_le_mul_of_nonneg_left (boundX l) hv,mul_le_mul_of_nonneg_left (boundW r) hw]
    · apply (le_max_right _ (C+s*N)).trans'
      apply nonneg_of_mul_nonneg_right (a := s) _ hs
      dsimp only [C,N]
      nlinarith only [H,mul_le_mul_of_nonneg_left (boundX h) hv,mul_le_mul_of_nonneg_left negW hw]
  have lim : Tendsto (fun s : ℝ => max (R+s*M) (C+s*N)) (𝓝[>] 0) (𝓝 (max R C)) := by
    have H : Continuous (fun s : ℝ => max (R+s*M) (C+s*N)) := by fun_prop
    have H' := (H.tendsto (0:ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa using H'
  have pos : 0 ≤ max R C := ge_of_tendsto lim (by filter_upwards [self_mem_nhdsWithin] with s hs; exact approx s hs)
  rcases le_max_iff.mp pos with hp | hp
  · exact Or.inl (sub_nonneg.mp hp)
  · exact Or.inr (sub_nonneg.mp hp)

/-- The work done by two directed weights is bounded by the triangle charge
when their resultant fits strictly inside the third rate. -/
theorem interior_work (hg : P2M.R113.gamma = Real.sqrt 2) {a b c : ℝ}
    (hc : 0 < c) (hβ : 0 ≤ formatBeta a b c) (p q l r : ℂ)
    (hp : 0 < ‖p‖) (hq : 0 < ‖q‖) (ha : ‖p‖ ≤ a) (hb : ‖q‖ ≤ b)
    (hsum : ‖p+q‖ < c) (hdiff : 0 < ‖p-q‖) :
    ⟪p,l⟫_ℝ + ⟪q,r⟫_ℝ ≤ formatBeta a b c/2 * perimeter3 dist l r 0 := by
  let D := 2*(‖p‖^2+‖q‖^2)-c^2
  have diff : D < ‖p-q‖^2 := by
    dsimp [D]
    linarith only [parallelogram_law_with_norm ℝ p q, pow_lt_pow_left₀ hsum (norm_nonneg _) (by decide +kernel : 2 ≠ 0)]
  have hsqrt : Real.sqrt D < ‖p-q‖ := (Real.sqrt_lt' hdiff).mpr diff
  obtain ⟨κ,hκs,hκd⟩ := exists_between hsqrt
  have hκ := (Real.sqrt_nonneg D).trans hκs.le
  have disk : 2*(‖p‖^2+‖q‖^2) < c^2+κ^2 := by
    have H := pow_lt_pow_left₀ hκs (Real.sqrt_nonneg D) (by decide +kernel : 2 ≠ 0)
    have Hd : D ≤ (Real.sqrt D)^2 := by rw [Real.sq_sqrt']; exact le_max_left ..
    dsimp [D] at Hd; linarith only [H,Hd]
  let X := ‖p‖⁻¹ • p
  let Y := ‖q‖⁻¹ • q
  have unit (z : ℂ) (hz : 0 < ‖z‖) : ‖‖z‖⁻¹ • z‖ = 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hz.le),inv_mul_cancel₀ hz.ne']
  have H := first_variation hp.le hq.le (X := X) (Y := Y) (unit p hp) (unit q hq) l r (p-q) fun s _ =>
    plane_bill hg _ (two_rays (unit p hp) (by rw [norm_smul,show ‖Y‖ = 1 from unit q hq,mul_one]; norm_num)) _ _ _ _ _ hp hq ha hb hc.le hβ hκ disk
  have xwork (z x : ℂ) (hz : 0 < ‖z‖) : ‖z‖*⟪‖z‖⁻¹ • z,x⟫_ℝ = ⟪z,x⟫_ℝ := by
    rw [real_inner_smul_left,← mul_assoc,mul_inv_cancel₀ hz.ne',one_mul]
  simp only [X,Y,xwork p _ hp,xwork q _ hq,← inner_sub_left,real_inner_self_eq_norm_sq] at H
  exact H.resolve_right (by nlinarith only [mul_lt_mul_of_pos_right hκd hdiff])

/-- Simultaneous contraction of the two vectors extends the work inequality
to the boundary of the third rate. -/
theorem boundary_work (hg : P2M.R113.gamma = Real.sqrt 2) {a b c : ℝ} (hc : 0 < c)
    (hβ : 0 ≤ formatBeta a b c) (p q l r : ℂ) (hp : 0 < ‖p‖) (hq : 0 < ‖q‖)
    (ha : ‖p‖ ≤ a) (hb : ‖q‖ ≤ b) (hsum : ‖p+q‖ ≤ c) (hdiff : 0 < ‖p-q‖) :
    ⟪p,l⟫_ℝ + ⟪q,r⟫_ℝ ≤ formatBeta a b c/2 * perimeter3 dist l r 0 := by
  let W := ⟪p,l⟫_ℝ + ⟪q,r⟫_ℝ
  have lim : Tendsto (fun s : ℝ => s*W) (𝓝[<] 1) (𝓝 W) := by
    simpa using (tendsto_id.mono_left (nhdsWithin_le_nhds (a := (1:ℝ)) (s := Set.Iio 1))).mul_const W
  apply le_of_tendsto lim
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (zero_lt_one' ℝ))] with s hs hs₀
  have hsp : 0 < s := hs₀
  have hs₁ : s < 1 := hs
  have scale (x : ℂ) : ‖s • x‖ = s*‖x‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos hsp]
  have under (x : ℂ) : s*‖x‖ ≤ ‖x‖ := mul_le_of_le_one_left (norm_nonneg x) hs₁.le
  have H := interior_work hg hc hβ (s • p) (s • q) l r
    (by rw [scale]; positivity) (by rw [scale]; positivity)
    ((scale p).trans_le ((under p).trans ha)) ((scale q).trans_le ((under q).trans hb))
    (by
      rw [← smul_add,scale]
      exact (mul_le_mul_of_nonneg_left hsum hsp.le).trans_lt (by simpa using mul_lt_mul_of_pos_right hs₁ hc))
    (by rw [← smul_sub,scale]; positivity)
  simpa only [W,real_inner_smul_left,mul_add] using H

end OM.Formats
