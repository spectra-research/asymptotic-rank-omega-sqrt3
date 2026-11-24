import Lib.OM.NNN18.Step
import Lib.OM.NNN12.Stars
import Lib.OM.NNN12.Powers


noncomputable section
open scoped BigOperators
open CoordinateTensor OM.NNN.Raw Foundations.PairUnitExponents
open OM.NNN12 (Shape DyadicTensor volume)
namespace OM.NNN18

def InTri (R : ℝ) (δ : Fin 3 → ℝ) : Prop := δ 0 + δ 1 + δ 2 = 0 ∧ ∀ i, δ i ≤ R

structure TrackFacts (P : Track) where
  R : ℝ
  hR : 0 < R
  tariff_nonneg : ∀ δ, InTri R δ → ∀ h j, 0 ≤ tariff P δ h j
  tariff_le_one : ∀ δ, InTri R δ → ∀ h j, tariff P δ h j ≤ 1
  seed : ∀ δ, InTri R δ → ∀ h j, star (theta P δ) h j ≤ tariff P δ h j + 1 / 2
  theta_mem : ∀ δ, InTri R δ → ∀ i, theta P δ i ∈ Set.Icc (0 : ℝ) 1
  theta_pos : ∀ δ, InTri R δ → ∀ i, 0 < theta P δ i
  slope : ∀ δ, InTri R δ → ∀ h i e, 0 ≤ e → NNN13.rawSlope (theta P δ) (parentsH P h e δ) i ≤ 0
  beta_le : ∀ δ, InTri R δ → ∀ h i e, i ≠ h → 0 ≤ e → e ≤ 1 / 25 → betaPackH P h e δ i ≤ 1
  form_ord : ∀ δ, InTri R δ → ∀ h (x : Fin 3 → ℝ), (∀ i, 0 ≤ x i) →
    ∀ e, 1 / 25 ≤ e → e ≤ 1 / 2 → 0 ≤ formH P false h e δ x
  form_pack : ∀ δ, InTri R δ → ∀ h (x : Fin 3 → ℝ), (∀ i, 0 ≤ x i) →
    ∀ e, 0 ≤ e → 0 ≤ formH P true h e δ x

lemma star_eq_starCoefficients (θ : Fin 3 → ℝ) (h : Fin 3) :
    star θ h = NNN13.starCoefficients θ h := by
  funext j; fin_cases h <;> fin_cases j <;> simp [star, other, NNN13.starCoefficients]

theorem star_affine (φ : PolMul.Spectral ℂ) (t : Fin 3 → ℝ)
    (hθ : ∀ i, Foundations.PairUnitExponents.theta φ i ≤ t i)
    (h : Fin 3) : NNN13.AffineBound φ (star t h) := by
  intro v U
  rw [star_eq_starCoefficients]
  fin_cases h
  · have := OM.NNN12.value_le_star_A φ v U t hθ
    simpa [NNN13.plane, NNN13.starCoefficients] using this.trans_eq (by ring_nf)
  · have := OM.NNN12.value_le_star_B φ v U t hθ
    simpa [NNN13.plane, NNN13.starCoefficients] using this.trans_eq (by ring_nf)
  · have := OM.NNN12.value_le_star_C φ v U t hθ
    simpa [NNN13.plane, NNN13.starCoefficients] using this.trans_eq (by ring_nf)

lemma cross_nonneg {p : Fin 3 → ℝ} (hp : ∀ j, 0 ≤ p j) (i : Fin 3) : 0 ≤ cross p i := by
  fin_cases i <;> simp [cross] <;> linarith [hp 0, hp 1, hp 2]

/-- The envelope `min_h C_h · v`. -/
def env (P : Track) (δ : Fin 3 → ℝ) (v : Shape) : ℝ :=
  NNN13.min3 (fun h => NNN13.plane (tariff P δ h) (fun j => (v j : ℝ)))

lemma env_le (P : Track) (δ : Fin 3 → ℝ) (v : Shape) (h : Fin 3) :
    env P δ v ≤ NNN13.plane (tariff P δ h) (fun j => (v j : ℝ)) := NNN13.min3_le _ h

lemma env_attained (P : Track) (δ : Fin 3 → ℝ) (v : Shape) :
    ∃ h, env P δ v = NNN13.plane (tariff P δ h) (fun j => (v j : ℝ)) := by
  unfold env NNN13.min3
  rcases min_choice (NNN13.plane (tariff P δ 0) (fun j => (v j : ℝ)))
    (min (NNN13.plane (tariff P δ 1) (fun j => (v j : ℝ)))
      (NNN13.plane (tariff P δ 2) (fun j => (v j : ℝ)))) with h | h
  · exact ⟨0, h⟩
  · rw [h]
    rcases min_choice (NNN13.plane (tariff P δ 1) (fun j => (v j : ℝ)))
      (NNN13.plane (tariff P δ 2) (fun j => (v j : ℝ))) with h' | h'
    · exact ⟨1, h'⟩
    · exact ⟨2, h'⟩

lemma env_nonneg (P : Track) (G : TrackFacts P) {δ : Fin 3 → ℝ} (hδ : InTri G.R δ) (v : Shape) :
    0 ≤ env P δ v := by
  obtain ⟨h, hh⟩ := env_attained P δ v
  rw [hh]
  have t0 := G.tariff_nonneg δ hδ h 0
  have t1 := G.tariff_nonneg δ hδ h 1
  have t2 := G.tariff_nonneg δ hδ h 2
  simp only [NNN13.plane]
  have := mul_nonneg t0 (Nat.cast_nonneg (v 0) : (0 : ℝ) ≤ v 0)
  have := mul_nonneg t1 (Nat.cast_nonneg (v 1) : (0 : ℝ) ≤ v 1)
  have := mul_nonneg t2 (Nat.cast_nonneg (v 2) : (0 : ℝ) ≤ v 2)
  linarith

lemma env_power (P : Track) (δ : Fin 3 → ℝ) (q : ℕ) (v : Shape) :
    env P δ (OM.NNN12.powerShape q v) = q * env P δ v := by
  have e : ∀ c : Fin 3 → ℝ, NNN13.plane c (fun j => ((OM.NNN12.powerShape q v j : ℕ) : ℝ)) =
      q * NNN13.plane c (fun j => (v j : ℝ)) := by
    intro c; simp only [NNN13.plane, OM.NNN12.powerShape, Nat.cast_mul]; ring
  simp only [env, NNN13.min3, e]
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  rw [mul_min_of_nonneg _ _ hq, mul_min_of_nonneg _ _ hq]

lemma plane_add_const (c x : Fin 3 → ℝ) (s : ℝ) :
    NNN13.plane (fun i => c i + s) x = NNN13.plane c x + s * (x 0 + x 1 + x 2) := by
  simp only [NNN13.plane]; ring

lemma volume_eq (v : Shape) : volume v = (v 0 : ℝ) + v 1 + v 2 := rfl

theorem focus_step (P : Track) (G : TrackFacts P) (TS : TriangleStep) (φ : PolMul.Spectral ℂ)
    {δ : Fin 3 → ℝ} (hδ : InTri G.R δ)
    (hθ : ∀ i, Foundations.PairUnitExponents.theta φ i ≤ theta P δ i) (hsum : ∑ i, theta P δ i ≤ 9 / 4)
    {ε : ℝ} (he0 : 0 ≤ ε) (he1 : ε ≤ 1 / 2)
    (hb : ∀ (v : Shape) (U : DyadicTensor v), value φ U ≤ (2 : ℝ) ^ (env P δ v + ε * volume v))
    (h : Fin 3) (v : Shape) (hv : ∀ i, 1 ≤ v i) (U : DyadicTensor v) :
    value φ U ≤ 2 * (2 : ℝ) ^ NNN13.plane (targetH P h (19 / 20) ε δ) (fun j => (v j : ℝ)) := by
  set F := NNN13.plane (targetH P h (19 / 20) ε δ) (fun j => (v j : ℝ))
  have hpar : ∀ i, NNN13.AffineBound φ (parentsH P h ε δ i) := by
    intro i
    by_cases hi : i = h
    · subst hi; simp only [parentsH, if_pos rfl]; exact star_affine φ _ hθ i
    · simp only [parentsH, if_neg hi]
      intro w W
      refine (hb w W).trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
      rw [plane_add_const, volume_eq]
      have := env_le P δ w i
      linarith
  have hF2 : (2 : ℝ) ^ F ≤ 2 * (2 : ℝ) ^ F := by
    have : (0 : ℝ) ≤ (2 : ℝ) ^ F := by positivity
    linarith
  by_cases hbase : ∀ i, F ≤ NNN13.plane (parentsH P h ε δ i) (fun j => (v j : ℝ))
  · have hxv : ∀ i, (0 : ℝ) ≤ (fun j => (v j : ℝ)) i := fun i => Nat.cast_nonneg _
    by_cases hε : 1 / 25 ≤ ε
    · have hgap := G.form_ord δ hδ h (fun j => (v j : ℝ)) hxv ε hε he1
      apply ord_step φ h (parentsH P h ε δ) (theta P δ) F hpar (G.theta_mem δ hδ) hsum hθ
        (fun i => G.slope δ hδ h i ε he0) v hv hbase
      have heq : formH P false h ε δ (fun j => (v j : ℝ)) = form h (theta P δ) (fun _ => 1)
          (parentsH P h ε δ) (fun i => ell (NNN13.rawSlope (theta P δ) (parentsH P h ε δ) i)) F
          (fun j => (v j : ℝ)) := by
        simp only [formH, Bool.false_eq_true, ↓reduceIte, args, div_one]
        rfl
      rwa [heq] at hgap
    · push_neg at hε
      have hgap := G.form_pack δ hδ h (fun j => (v j : ℝ)) hxv ε he0
      have hβpos : ∀ i, 0 < betaPackH P h ε δ i := by
        intro i
        by_cases hi : i = h
        · simp [betaPackH, hi]
        · have h1 := G.theta_pos δ hδ i
          have h2 : 0 ≤ cross (fun j => tariff P δ i j + ε) i :=
            cross_nonneg (fun j => by have := G.tariff_nonneg δ hδ i j; linarith) i
          simp only [betaPackH, if_neg hi, parentsH]
          linarith
      apply TS h φ (copies 1 h v) (parentsH P h ε δ) (theta P δ) (betaPackH P h ε δ) F hpar
        (G.theta_mem δ hδ) hsum hθ (by simp [betaPackH]) hβpos
        (fun i hi => ⟨by simp [betaPackH, if_neg hi, cross, NNN13.cross],
          G.beta_le δ hδ h i ε hi he0 hε.le⟩)
        (fun i => G.slope δ hδ h i ε he0)
        (fun i => by simp only [copies]; have := hv i; split_ifs <;> omega) v hbase
      rw [packedGap_copies]
      have heq : formH P true h ε δ (fun j => (v j : ℝ)) = form h (theta P δ) (betaPackH P h ε δ)
          (parentsH P h ε δ) (fun i => ell ((theta P δ i - NNN13.cross (parentsH P h ε δ i) i) /
            betaPackH P h ε δ i)) F (fun j => (v j : ℝ)) := by
        simp only [formH, ↓reduceIte, args]
        rfl
      rw [heq] at hgap
      simpa using hgap
  · push_neg at hbase
    obtain ⟨i, hi⟩ := hbase
    exact ((hpar i v U).trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) hi.le)).trans hF2

/-- The step on every shape, with the uniform constant `128` (zero coordinates by padding). -/
theorem env_step (P : Track) (G : TrackFacts P) (TS : TriangleStep) (φ : PolMul.Spectral ℂ)
    {δ : Fin 3 → ℝ} (hδ : InTri G.R δ)
    (hθ : ∀ i, Foundations.PairUnitExponents.theta φ i ≤ theta P δ i) (hsum : ∑ i, theta P δ i ≤ 9 / 4)
    {ε : ℝ} (he0 : 0 ≤ ε) (he1 : ε ≤ 1 / 2)
    (hb : ∀ (v : Shape) (U : DyadicTensor v), value φ U ≤ (2 : ℝ) ^ (env P δ v + ε * volume v))
    (v : Shape) (U : DyadicTensor v) :
    value φ U ≤ 128 * (2 : ℝ) ^ (env P δ v + 19 / 20 * ε * volume v) := by
  have pos_case : ∀ (w : Shape), (∀ i, 1 ≤ w i) → ∀ W : DyadicTensor w,
      value φ W ≤ 2 * (2 : ℝ) ^ (env P δ w + 19 / 20 * ε * volume w) := by
    intro w hw W
    obtain ⟨h, hh⟩ := env_attained P δ w
    have := focus_step P G TS φ hδ hθ hsum he0 he1 hb h w hw W
    have e : NNN13.plane (targetH P h (19 / 20) ε δ) (fun j => (w j : ℝ)) =
        env P δ w + 19 / 20 * ε * volume w := by
      rw [hh]; simp only [targetH, NNN13.plane, volume_eq]; ring
    rwa [e] at this
  by_cases hv : ∀ i, 1 ≤ v i
  · have := pos_case v hv U
    have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ (env P δ v + 19 / 20 * ε * volume v) := by positivity
    linarith
  · let w : Shape := fun i => max (v i) 1
    have hvw : ∀ i, v i ≤ w i := fun i => le_max_left _ _
    obtain ⟨W, hW⟩ := exists_pad φ hvw U
    have hw : ∀ i, 1 ≤ w i := fun i => le_max_right _ _
    have hWb := pos_case w hw W
    -- the envelope and the volume grow by at most 3
    have hd : ∀ i, (w i : ℝ) ≤ v i + 1 := by
      intro i; simp only [w]; have := Nat.max_le.2 ⟨Nat.le_succ (v i), Nat.succ_le_succ (Nat.zero_le (v i))⟩
      exact_mod_cast (le_trans (le_of_eq rfl) (by omega : max (v i) 1 ≤ v i + 1))
    obtain ⟨h, hh⟩ := env_attained P δ v
    have henv : env P δ w ≤ env P δ v + 3 := by
      refine (env_le P δ w h).trans ?_
      rw [hh]
      simp only [NNN13.plane]
      have t0 := G.tariff_le_one δ hδ h 0
      have t1 := G.tariff_le_one δ hδ h 1
      have t2 := G.tariff_le_one δ hδ h 2
      have n0 := G.tariff_nonneg δ hδ h 0
      have n1 := G.tariff_nonneg δ hδ h 1
      have n2 := G.tariff_nonneg δ hδ h 2
      have := mul_le_mul_of_nonneg_left (sub_le_iff_le_add.2 (hd 0)) n0
      have := mul_le_mul_of_nonneg_left (sub_le_iff_le_add.2 (hd 1)) n1
      have := mul_le_mul_of_nonneg_left (sub_le_iff_le_add.2 (hd 2)) n2
      nlinarith
    have hvol : volume w ≤ volume v + 3 := by
      simp only [volume_eq]; linarith [hd 0, hd 1, hd 2]
    have hexp : env P δ w + 19 / 20 * ε * volume w ≤ (env P δ v + 19 / 20 * ε * volume v) + 6 := by
      have : 19 / 20 * ε * volume w ≤ 19 / 20 * ε * volume v + 3 := by
        have hq : 0 ≤ 19 / 20 * ε := by positivity
        nlinarith
      linarith
    calc value φ U ≤ value φ W := hW
      _ ≤ 2 * (2 : ℝ) ^ (env P δ w + 19 / 20 * ε * volume w) := hWb
      _ ≤ 2 * (2 : ℝ) ^ ((env P δ v + 19 / 20 * ε * volume v) + 6) := by
          gcongr; norm_num
      _ = 128 * (2 : ℝ) ^ (env P δ v + 19 / 20 * ε * volume v) := by
          rw [Real.rpow_add (by norm_num)]; norm_num; ring

theorem tariffs_valid (P : Track) (G : TrackFacts P) (TS : TriangleStep) (φ : PolMul.Spectral ℂ)
    {δ : Fin 3 → ℝ} (hδ : InTri G.R δ)
    (hθ : ∀ i, Foundations.PairUnitExponents.theta φ i ≤ theta P δ i) (hsum : ∑ i, theta P δ i ≤ 9 / 4)
    (h : Fin 3) (v : Shape) (U : DyadicTensor v) :
    value φ U ≤ (2 : ℝ) ^ NNN13.plane (tariff P δ h) (fun j => (v j : ℝ)) := by
  have hF : ∀ w, 0 ≤ env P δ w := env_nonneg P G hδ
  -- seed: the excess is at most 1/2
  have hseed : ∀ (w : Shape) (W : DyadicTensor w),
      value φ W ≤ (2 : ℝ) ^ (env P δ w + 1 / 2 * volume w) := by
    intro w W
    obtain ⟨h', hh'⟩ := env_attained P δ w
    refine (star_affine φ _ hθ h' w W).trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
    rw [hh']
    simp only [NNN13.plane, volume_eq]
    have s0 := G.seed δ hδ h' 0
    have s1 := G.seed δ hδ h' 1
    have s2 := G.seed δ hδ h' 2
    have := mul_le_mul_of_nonneg_right s0 (Nat.cast_nonneg (w 0) : (0 : ℝ) ≤ w 0)
    have := mul_le_mul_of_nonneg_right s1 (Nat.cast_nonneg (w 1) : (0 : ℝ) ≤ w 1)
    have := mul_le_mul_of_nonneg_right s2 (Nat.cast_nonneg (w 2) : (0 : ℝ) ≤ w 2)
    nlinarith
  set E := OM.NNN12.excess φ (env P δ)
  have hE0 : 0 ≤ E := OM.NNN12.excess_nonneg φ hF
  have hE1 : E ≤ 1 / 2 := OM.NNN12.excess_le_of_bound φ _ (by norm_num) hseed
  have hb : ∀ (w : Shape) (W : DyadicTensor w), value φ W ≤ (2 : ℝ) ^ (env P δ w + E * volume w) :=
    OM.NNN12.value_le_excess φ hF
  -- one step at the actual excess
  have hstep : ∀ (w : Shape) (W : DyadicTensor w),
      value φ W ≤ (2 : ℝ) ^ (env P δ w + 19 / 20 * E * volume w) := by
    apply OM.NNN12.remove_uniform_constant φ (C := 128)
    · intro q w
      rw [env_power, OM.NNN12.volume_power]; ring
    · exact env_step P G TS φ hδ hθ hsum hE0 hE1 hb
  have hE : E ≤ 19 / 20 * E := OM.NNN12.excess_le_of_bound φ _ (by positivity) hstep
  have hE00 : E = 0 := by linarith
  have := hb v U
  rw [hE00, zero_mul, add_zero] at this
  exact this.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (env_le P δ v h))

theorem tri3_affine_le {R α b0 b1 b2 c : ℝ} (hR : 0 < R) {δ : Fin 3 → ℝ} (hδ : InTri R δ)
    (h0 : α + b0 * (-2 * R) + b1 * R + b2 * R ≤ c) (h1 : α + b0 * R + b1 * (-2 * R) + b2 * R ≤ c)
    (h2 : α + b0 * R + b1 * R + b2 * (-2 * R) ≤ c) : α + b0 * δ 0 + b1 * δ 1 + b2 * δ 2 ≤ c := by
  obtain ⟨hs, hle⟩ := hδ
  have key : 3 * R * (α + b0 * δ 0 + b1 * δ 1 + b2 * δ 2 - c) =
      (R - δ 0) * (α + b0 * (-2 * R) + b1 * R + b2 * R - c)
      + (R - δ 1) * (α + b0 * R + b1 * (-2 * R) + b2 * R - c)
      + (R - δ 2) * (α + b0 * R + b1 * R + b2 * (-2 * R) - c) := by
    have : δ 2 = -δ 0 - δ 1 := by linarith
    rw [this]; ring
  have t0 := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 (hle 0)) (sub_nonpos.2 h0)
  have t1 := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 (hle 1)) (sub_nonpos.2 h1)
  have t2 := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 (hle 2)) (sub_nonpos.2 h2)
  have : 3 * R * (α + b0 * δ 0 + b1 * δ 1 + b2 * δ 2 - c) ≤ 0 := by rw [key]; linarith
  have h3 : 0 < 3 * R := by linarith
  nlinarith

theorem tri3_affine_ge {R α b0 b1 b2 c : ℝ} (hR : 0 < R) {δ : Fin 3 → ℝ} (hδ : InTri R δ)
    (h0 : c ≤ α + b0 * (-2 * R) + b1 * R + b2 * R) (h1 : c ≤ α + b0 * R + b1 * (-2 * R) + b2 * R)
    (h2 : c ≤ α + b0 * R + b1 * R + b2 * (-2 * R)) : c ≤ α + b0 * δ 0 + b1 * δ 1 + b2 * δ 2 := by
  have := tri3_affine_le (α := -α) (b0 := -b0) (b1 := -b1) (b2 := -b2) (c := -c) hR hδ
    (by linarith) (by linarith) (by linarith)
  linarith

lemma forall_fin3_2 {p : Fin 3 → Fin 3 → Prop} (h00 : p 0 0) (h01 : p 0 1) (h02 : p 0 2)
    (h10 : p 1 0) (h11 : p 1 1) (h12 : p 1 2) (h20 : p 2 0) (h21 : p 2 1) (h22 : p 2 2) :
    ∀ h j, p h j := by
  intro h j; fin_cases h <;> fin_cases j <;> assumption

end OM.NNN18
