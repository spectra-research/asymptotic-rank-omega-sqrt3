import Lib.OM.NNN30.Geom.Cone
import Lib.OM.NNN30.Geom.Quadrant

/-! # Two directions at the minimising point

Fix a midpoint space `S`, a point `o` and two terminals `pa`, `pb`.  In the cone at `o`:

* `ray p s` (`s ≥ 0`) is the sequence of dyadic points at fraction `≈ s 2^{-n}` on `[o, p]`
  (level `2n`), so `ρ(O, ray p s) = s d(o,p)` and `ρ(ray p s, ray p t) = |s - t| d(o,p)`;
* `δ = lim 2^n d(x_n, y_n)` with `x_n = (m o)^[n] pa`, `y_n = (m o)^[n] pb` (an antitone sequence,
  so the limit exists, and `δ ≤ d(pa, pb)`, which is (11) at `t = 2^{-n}`);
* `ρ(ray pa s, ray pb s) = s δ` (`f_eq`): at `s = 2^{±K}` from the convergence of `2^n d(x_n,y_n)`,
  in between by Busemann convexity (11) in the cone along `[O, ray p T]`;
* `J (u, v)` is the point at fraction `v / (u+v)` on `[ray pa (u+v), ray pb (u+v)]`; midpoints of
  `J`-points are `J`-points of the affine midpoints (`J_mid`, by (9) and uniqueness of geodesic
  points), so `N z z' = ρ(J z, J z')` satisfies the hypotheses of the quadrant lemma;
* the minimising property (5) of `o` gives, at every cone point `Q`,
  `ρ(Q, ray pa 2^K) + ρ(Q, ray pb 2^K) + ρ(Q, O) ≥ 2^K (d(o,pa) + d(o,pb))` (`fermat_cone`). -/

noncomputable section

open Filter Topology

namespace OM.NNN30.Geom

open ConePt

variable {X : Type*} (S : MidSpace X) (o : X)

/-- `(m o)^[n] p`: the point at fraction `2^{-n}` from `o` to `p`. -/
def hx (p : X) (n : ℕ) : X := (S.m o)^[n] p

lemma hx_eq_geo (p : X) (n : ℕ) : hx S o p n = S.geo o p n 1 := by
  have := S.geo_pow n 0 o p
  simp only [add_zero, pow_zero] at this
  exact this.symm

lemma hx_right (p : X) (n : ℕ) : S.d (hx S o p n) p = (1 - 1 / 2 ^ n) * S.d o p := by
  rw [hx_eq_geo, S.geo_right n o p Nat.one_le_two_pow]
  simp

lemma hx_succ (p : X) (n : ℕ) : hx S o p (n + 1) = S.m o (hx S o p n) := by
  simp only [hx, Function.iterate_succ_apply']

section psi

variable (pa pb : X)

/-- `ψ n = 2^n d(x_n, y_n)`. -/
def psi (n : ℕ) : ℝ := 2 ^ n * S.d (hx S o pa n) (hx S o pb n)

lemma psi_nonneg (n : ℕ) : 0 ≤ psi S o pa pb n := mul_nonneg (by positivity) (S.d_nonneg _ _)

lemma psi_anti : Antitone (psi S o pa pb) := by
  apply antitone_nat_of_succ_le
  intro n
  simp only [psi, hx_succ]
  have := S.ax2 o (hx S o pa n) (hx S o pb n)
  have h2n : (0 : ℝ) ≤ 2 ^ n := by positivity
  have := mul_le_mul_of_nonneg_left this h2n
  rw [pow_succ]
  nlinarith

/-- The limit `δ` of `ψ`. -/
def delta : ℝ := ⨅ n, psi S o pa pb n

lemma psi_bdd : BddBelow (Set.range (psi S o pa pb)) :=
  ⟨0, by rintro _ ⟨n, rfl⟩; exact psi_nonneg S o pa pb n⟩

lemma tendsto_psi : Tendsto (psi S o pa pb) atTop (𝓝 (delta S o pa pb)) :=
  tendsto_atTop_ciInf (psi_anti S o pa pb) (psi_bdd S o pa pb)

lemma delta_nonneg : 0 ≤ delta S o pa pb := le_ciInf (psi_nonneg S o pa pb)

/-- (12) for the two rays at `t = 2^{-n}`: `δ ≤ d(pa, pb)`. -/
lemma delta_le : delta S o pa pb ≤ S.d pa pb := by
  have h1 : delta S o pa pb ≤ psi S o pa pb 0 := ciInf_le (psi_bdd S o pa pb) 0
  have h2 : psi S o pa pb 0 = S.d pa pb := by simp [psi, hx]
  linarith

end psi

/-! ## The cone points -/

/-- The base point `O` of the cone. -/
def O : ConePt S o := ⟨fun _ => o, ⟨0, fun n => by simp [S.d_self]⟩⟩

/-- Numerator of the ray points (level `2n`). -/
def rfrac (s : ℝ) (n : ℕ) : ℕ := min ⌊s * 2 ^ n⌋₊ (2 ^ (2 * n))

lemma rfrac_le (s : ℝ) (n : ℕ) : rfrac s n ≤ 2 ^ (2 * n) := min_le_right _ _

lemma floor_le_abs (x : ℝ) : (⌊x⌋₊ : ℝ) ≤ |x| := by
  rcases le_total 0 x with h | h
  · exact (Nat.floor_le h).trans (le_abs_self x)
  · rw [Nat.floor_of_nonpos h]; simp

lemma pow_two_mul (n : ℕ) : (2 : ℝ) ^ (2 * n) = 2 ^ n * 2 ^ n := by
  rw [two_mul, pow_add]

/-- Ray points: `ray p s` represents the point at distance `s d(o,p)` from `O` towards `p`. -/
def ray (p : X) (s : ℝ) : ConePt S o where
  seq n := S.geo o p (2 * n) (rfrac s n)
  bdd := ⟨|s| * S.d o p, fun n => by
    rw [S.d_comm, S.geo_left _ _ _ (rfrac_le s n)]
    have h2n : (0 : ℝ) < 2 ^ n := by positivity
    have hk : (rfrac s n : ℝ) ≤ |s| * 2 ^ n := by
      have := floor_le_abs (s * 2 ^ n)
      rw [abs_mul, abs_of_pos h2n] at this
      exact (Nat.cast_le.2 (min_le_left _ _)).trans this
    have e : (2 : ℝ) ^ n * ((rfrac s n : ℝ) / 2 ^ (2 * n) * S.d o p) =
        (rfrac s n : ℝ) / 2 ^ n * S.d o p := by
      rw [pow_two_mul]; field_simp
    rw [e]
    have hD := S.d_nonneg o p
    have : (rfrac s n : ℝ) / 2 ^ n ≤ |s| := by rw [div_le_iff₀ h2n]; exact hk
    nlinarith⟩

lemma rfrac_eventually {s : ℝ} : ∃ N, ∀ n, N ≤ n → rfrac s n = ⌊s * 2 ^ n⌋₊ := by
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt s (by norm_num : (1 : ℝ) < 2)
  refine ⟨N, fun n hn => min_eq_left (Nat.floor_le_of_le ?_)⟩
  have h1 : (2 : ℝ) ^ N ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
  push_cast
  rw [pow_two_mul]
  have : (0 : ℝ) < 2 ^ n := by positivity
  nlinarith

lemma tendsto_rfrac {s : ℝ} (hs : 0 ≤ s) :
    Tendsto (fun n => (rfrac s n : ℝ) / 2 ^ n) (U : Filter ℕ) (𝓝 s) := by
  obtain ⟨N, hN⟩ := rfrac_eventually (s := s)
  refine ((tendsto_floor_div hs).mono_left U_le_atTop).congr' ?_
  filter_upwards [eventually_U N (fun n hn => hN n hn)] with n hn
  rw [hn]

lemma sd_O_ray (p : X) (s : ℝ) (n : ℕ) :
    sd (O S o) (ray S o p s) n = (rfrac s n : ℝ) / 2 ^ n * S.d o p := by
  simp only [sd, O, ray]
  rw [S.geo_left _ _ _ (rfrac_le s n), pow_two_mul]
  field_simp

lemma ρ_O_ray (p : X) {s : ℝ} (hs : 0 ≤ s) : ρ (O S o) (ray S o p s) = s * S.d o p :=
  ρ_eq (((tendsto_rfrac hs).mul_const _).congr (fun n => (sd_O_ray S o p s n).symm))

lemma ρ_ray_ray (p : X) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ρ (ray S o p s) (ray S o p t) = |s - t| * S.d o p := by
  apply ρ_eq
  have h := (((tendsto_rfrac hs).sub (tendsto_rfrac ht)).abs).mul_const (S.d o p)
  refine h.congr (fun n => ?_)
  simp only [sd, ray]
  rw [S.geo_same _ _ _ (rfrac_le s n) (rfrac_le t n), pow_two_mul, ← sub_div, abs_div,
    abs_of_pos (by positivity : (0 : ℝ) < 2 ^ n), abs_sub_comm]
  field_simp

lemma ray_pow_seq (p : X) (K : ℕ) {n : ℕ} (hn : K ≤ n) :
    (ray S o p (2 ^ K)).seq n = hx S o p (n - K) := by
  simp only [ray, rfrac]
  have e : (2 : ℝ) ^ K * 2 ^ n = ((2 ^ (K + n) : ℕ) : ℝ) := by push_cast; ring
  have h2 : 2 ^ (K + n) ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [e, Nat.floor_natCast, min_eq_left h2]
  have h3 : 2 * n = (n - K) + (K + n) := by omega
  rw [h3, S.geo_pow]
  rfl

lemma ray_invpow_seq (p : X) (K : ℕ) {n : ℕ} (hn : K ≤ n) :
    (ray S o p (1 / 2 ^ K)).seq n = hx S o p (n + K) := by
  simp only [ray, rfrac]
  have e0 : (2 : ℝ) ^ n = 2 ^ (n - K) * 2 ^ K := by rw [← pow_add, Nat.sub_add_cancel hn]
  have e : (1 / (2 : ℝ) ^ K) * 2 ^ n = ((2 ^ (n - K) : ℕ) : ℝ) := by
    rw [e0]; push_cast; field_simp
  have h2 : 2 ^ (n - K) ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [e, Nat.floor_natCast, min_eq_left h2]
  have h3 : 2 * n = (n + K) + (n - K) := by omega
  rw [h3, S.geo_pow]
  rfl

section two

variable (pa pb : X)

lemma ρ_ray_pow (K : ℕ) :
    ρ (ray S o pa (2 ^ K)) (ray S o pb (2 ^ K)) = 2 ^ K * delta S o pa pb := by
  apply ρ_eq
  have h := ((tendsto_psi S o pa pb).comp (tendsto_sub_atTop_nat K)).const_mul ((2 : ℝ) ^ K)
  refine (h.mono_left U_le_atTop).congr' ?_
  filter_upwards [eventually_U K (fun n hn => hn)] with n hn
  simp only [Function.comp, psi, sd]
  rw [ray_pow_seq S o pa K hn, ray_pow_seq S o pb K hn, ← mul_assoc, ← pow_add,
    Nat.add_sub_cancel' hn]

lemma ρ_ray_invpow (K : ℕ) :
    ρ (ray S o pa (1 / 2 ^ K)) (ray S o pb (1 / 2 ^ K)) = delta S o pa pb / 2 ^ K := by
  apply ρ_eq
  have h := ((tendsto_psi S o pa pb).comp (tendsto_add_atTop_nat K)).div_const ((2 : ℝ) ^ K)
  refine (h.mono_left U_le_atTop).congr' ?_
  filter_upwards [eventually_U K (fun n hn => hn)] with n hn
  simp only [Function.comp, psi, sd]
  rw [ray_invpow_seq S o pa K hn, ray_invpow_seq S o pb K hn, pow_add]
  field_simp

/-- The minimising property (5) of `o`, transported to the cone. -/
lemma fermat_cone (pc : X)
    (hmin : ∀ q, S.d o pa + S.d o pb + S.d o pc ≤ S.d q pa + S.d q pb + S.d q pc)
    (Q : ConePt S o) (K : ℕ) :
    2 ^ K * (S.d o pa + S.d o pb) ≤
      ρ Q (ray S o pa (2 ^ K)) + ρ Q (ray S o pb (2 ^ K)) + ρ Q (O S o) := by
  refine le_of_tendsto_of_tendsto tendsto_const_nhds
    (((tendsto_ρ _ _).add (tendsto_ρ _ _)).add (tendsto_ρ _ _)) ?_
  filter_upwards [eventually_U K (fun n hn => hn)] with n hn
  simp only [sd, O]
  rw [ray_pow_seq S o pa K hn, ray_pow_seq S o pb K hn]
  have h1 := S.d_tri (Q.seq n) (hx S o pa (n - K)) pa
  have h2 := S.d_tri (Q.seq n) (hx S o pb (n - K)) pb
  have h3 := S.d_tri (Q.seq n) o pc
  have h4 := hmin (Q.seq n)
  rw [hx_right] at h1 h2
  have hp : (0 : ℝ) < 2 ^ (n - K) := by positivity
  have e1 : (1 - 1 / 2 ^ (n - K)) * S.d o pa = S.d o pa - S.d o pa / 2 ^ (n - K) := by ring
  have e2 : (1 - 1 / 2 ^ (n - K)) * S.d o pb = S.d o pb - S.d o pb / 2 ^ (n - K) := by ring
  rw [e1] at h1
  rw [e2] at h2
  have key : (S.d o pa + S.d o pb) / 2 ^ (n - K) ≤ S.d (Q.seq n) (hx S o pa (n - K)) +
      S.d (Q.seq n) (hx S o pb (n - K)) + S.d (Q.seq n) o := by
    rw [add_div]; linarith
  rw [div_le_iff₀ hp] at key
  have e : (2 : ℝ) ^ n = 2 ^ K * 2 ^ (n - K) := by rw [← pow_add, Nat.add_sub_cancel' hn]
  calc 2 ^ K * (S.d o pa + S.d o pb)
      ≤ 2 ^ K * ((S.d (Q.seq n) (hx S o pa (n - K)) + S.d (Q.seq n) (hx S o pb (n - K)) +
          S.d (Q.seq n) o) * 2 ^ (n - K)) := mul_le_mul_of_nonneg_left key (by positivity)
    _ = _ := by rw [e]; ring

/-! ## `ρ(ray pa s, ray pb s) = s δ` -/

lemma ray_onSeg (p : X) {s T : ℝ} (hs : 0 ≤ s) (hsT : s ≤ T) (hT : 0 < T) :
    (coneSpace S o).OnSeg (O S o) (ray S o p T) (ray S o p s) (s / T) := by
  constructor
  · show ρ _ _ = s / T * ρ _ _
    rw [ρ_O_ray S o p hs, ρ_O_ray S o p hT.le]; field_simp
  · show ρ _ _ = (1 - s / T) * ρ _ _
    rw [ρ_ray_ray S o p hs hT.le, ρ_O_ray S o p hT.le, abs_of_nonpos (by linarith)]
    field_simp; ring

lemma f_le_of {s T : ℝ} (hs : 0 ≤ s) (hsT : s ≤ T) (hT : 0 < T) :
    ρ (ray S o pa s) (ray S o pb s) ≤ s / T * ρ (ray S o pa T) (ray S o pb T) := by
  have := onSeg_bus (div_nonneg hs hT.le) (div_le_one_of_le₀ hsT hT.le)
    (ray_onSeg S o pa hs hsT hT) (ray_onSeg S o pb hs hsT hT)
  have h0 : ρ (O S o) (O S o) = 0 := (coneSpace S o).d_self _
  rw [h0, mul_zero, zero_add] at this
  exact this

lemma f_eq {s : ℝ} (hs : 0 ≤ s) :
    ρ (ray S o pa s) (ray S o pb s) = s * delta S o pa pb := by
  have hd := delta_nonneg S o pa pb
  rcases hs.lt_or_eq with hs | hs
  · apply le_antisymm
    · obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt s (by norm_num : (1 : ℝ) < 2)
      have := f_le_of S o pa pb hs.le hK.le (by positivity)
      rw [ρ_ray_pow] at this
      calc _ ≤ _ := this
        _ = s * delta S o pa pb := by field_simp
    · obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one hs (by norm_num : (1 / 2 : ℝ) < 1)
      rw [one_div_pow] at hK
      have := f_le_of S o pa pb (s := 1 / 2 ^ K) (T := s) (by positivity) hK.le hs
      rw [ρ_ray_invpow] at this
      have h2K : (0 : ℝ) < 2 ^ K := by positivity
      have hpos : (0 : ℝ) < 2 ^ K * s := by positivity
      have := mul_le_mul_of_nonneg_left this hpos.le
      have e1 : 2 ^ K * s * (delta S o pa pb / 2 ^ K) = s * delta S o pa pb := by field_simp
      have e2 : 2 ^ K * s * (1 / 2 ^ K / s * ρ (ray S o pa s) (ray S o pb s)) =
          ρ (ray S o pa s) (ray S o pb s) := by field_simp
      rw [e1, e2] at this
      exact this
  · subst hs
    have h1 := ρ_O_ray S o pa (le_refl (0 : ℝ))
    have h2 := ρ_O_ray S o pb (le_refl (0 : ℝ))
    have t := (coneSpace S o).d_tri (ray S o pa 0) (O S o) (ray S o pb 0)
    have c := (coneSpace S o).d_comm (ray S o pa 0) (O S o)
    have n0 := (coneSpace S o).d_nonneg (ray S o pa 0) (ray S o pb 0)
    simp only [coneSpace_d] at t c n0
    rw [zero_mul] at h1 h2 ⊢
    linarith

/-! ## The plane `J` -/

/-- `J (u, v)`: the point at fraction `v / (u + v)` on `[ray pa (u+v), ray pb (u+v)]`. -/
def J (z : ℝ × ℝ) : ConePt S o :=
  cgeo (ray S o pa (z.1 + z.2)) (ray S o pb (z.1 + z.2)) (z.2 / (z.1 + z.2))

lemma J_frac {z : ℝ × ℝ} (hz : InQ z) : 0 ≤ z.2 / (z.1 + z.2) ∧ z.2 / (z.1 + z.2) ≤ 1 := by
  constructor
  · exact div_nonneg hz.2 (add_nonneg hz.1 hz.2)
  · rcases (add_nonneg hz.1 hz.2).lt_or_eq with h | h
    · rw [div_le_one h]; linarith [hz.1]
    · rw [← h, div_zero]; norm_num

lemma J_left {z : ℝ × ℝ} (hz : InQ z) :
    ρ (ray S o pa (z.1 + z.2)) (J S o pa pb z) = z.2 * delta S o pa pb := by
  obtain ⟨t0, t1⟩ := J_frac hz
  rw [J, ρ_cgeo_left _ _ t0 t1, f_eq S o pa pb (add_nonneg hz.1 hz.2)]
  rcases (add_nonneg hz.1 hz.2).lt_or_eq with h | h
  · field_simp
  · have h1 : z.2 = 0 := by linarith [hz.1, hz.2]
    rw [h1]; simp

lemma J_right {z : ℝ × ℝ} (hz : InQ z) :
    ρ (J S o pa pb z) (ray S o pb (z.1 + z.2)) = z.1 * delta S o pa pb := by
  obtain ⟨t0, t1⟩ := J_frac hz
  rw [J, ρ_cgeo_right _ _ t0 t1, f_eq S o pa pb (add_nonneg hz.1 hz.2)]
  rcases (add_nonneg hz.1 hz.2).lt_or_eq with h | h
  · field_simp; ring
  · have h1 : z.1 = 0 := by linarith [hz.1, hz.2]
    have h2 : z.2 = 0 := by linarith [hz.1, hz.2]
    rw [h1, h2]; simp

lemma J_onSeg {z : ℝ × ℝ} (hz : InQ z) {s : ℝ} (hs : z.1 + z.2 = s) :
    (coneSpace S o).OnSeg (ray S o pa s) (ray S o pb s) (J S o pa pb z) (z.2 / s) := by
  obtain ⟨t0, t1⟩ := J_frac hz
  rw [hs] at t0 t1
  have := cgeo_onSeg (ray S o pa s) (ray S o pb s) t0 t1
  rw [J, hs]
  exact this

lemma ray_mid (p : X) {s s' : ℝ} (hs : 0 ≤ s) (hs' : 0 ≤ s') :
    ρ (M (ray S o p s) (ray S o p s')) (ray S o p ((s + s') / 2)) = 0 := by
  have hσ : 0 ≤ (s + s') / 2 := by positivity
  have h1 : (coneSpace S o).OnSeg (ray S o p s) (ray S o p s') (ray S o p ((s + s') / 2)) (1 / 2) := by
    constructor
    · show ρ _ _ = 1 / 2 * ρ _ _
      rw [ρ_ray_ray S o p hs hσ, ρ_ray_ray S o p hs hs']
      have : s - (s + s') / 2 = (s - s') / 2 := by ring
      rw [this, abs_div, abs_two]; ring
    · show ρ _ _ = (1 - 1 / 2) * ρ _ _
      rw [ρ_ray_ray S o p hσ hs', ρ_ray_ray S o p hs hs']
      have : (s + s') / 2 - s' = (s - s') / 2 := by ring
      rw [this, abs_div, abs_two]; ring
  exact (coneSpace S o).onSeg_unique (by norm_num) (by norm_num)
    ((coneSpace S o).onSeg_mid _ _) h1

/-- Midpoints of `J`-points are `J`-points of affine midpoints. -/
lemma J_mid {z z' : ℝ × ℝ} (hz : InQ z) (hz' : InQ z') :
    ρ (M (J S o pa pb z) (J S o pa pb z')) (J S o pa pb (mid z z')) = 0 := by
  have C1 := (coneSpace S o).d_nonneg
  have hmQ : InQ (mid z z') := QHyp.inQ_mid hz hz'
  have hs0 : 0 ≤ z.1 + z.2 := add_nonneg hz.1 hz.2
  have hs0' : 0 ≤ z'.1 + z'.2 := add_nonneg hz'.1 hz'.2
  have hσ : (mid z z').1 + (mid z z').2 = ((z.1 + z.2) + (z'.1 + z'.2)) / 2 := by
    simp only [mid]; ring
  rcases (add_nonneg hs0 hs0').lt_or_eq with hpos | hzero
  · set s := z.1 + z.2 with hs
    set s' := z'.1 + z'.2 with hs'
    set σ := (s + s') / 2 with hσdef
    have hσpos : 0 < σ := by rw [hσdef]; linarith
    have hX := ray_mid S o pa hs0 hs0'
    have hY := ray_mid S o pb hs0 hs0'
    rw [← hσdef] at hX hY
    have hd := delta_nonneg S o pa pb
    -- distances from the midpoint `W` to the ends of `[ray pa σ, ray pb σ]`
    have wX : ρ (M (J S o pa pb z) (J S o pa pb z')) (ray S o pa σ) ≤
        (z.2 + z'.2) / 2 * delta S o pa pb := by
      have e := (coneSpace S o).d_congr_right (M (J S o pa pb z) (J S o pa pb z')) hX
      simp only [coneSpace_d] at e
      rw [← e]
      have b := (coneSpace S o).bus (J S o pa pb z) (J S o pa pb z') (ray S o pa s) (ray S o pa s')
      simp only [coneSpace_d, coneSpace_m] at b
      have c1 := (coneSpace S o).d_comm (J S o pa pb z) (ray S o pa s)
      have c2 := (coneSpace S o).d_comm (J S o pa pb z') (ray S o pa s')
      simp only [coneSpace_d] at c1 c2
      rw [c1, c2, J_left S o pa pb hz, J_left S o pa pb hz'] at b
      linarith
    have wY : ρ (M (J S o pa pb z) (J S o pa pb z')) (ray S o pb σ) ≤
        (z.1 + z'.1) / 2 * delta S o pa pb := by
      have e := (coneSpace S o).d_congr_right (M (J S o pa pb z) (J S o pa pb z')) hY
      simp only [coneSpace_d] at e
      rw [← e]
      have b := (coneSpace S o).bus (J S o pa pb z) (J S o pa pb z') (ray S o pb s) (ray S o pb s')
      simp only [coneSpace_d, coneSpace_m] at b
      rw [J_right S o pa pb hz, J_right S o pa pb hz'] at b
      linarith
    have hf := f_eq S o pa pb hσpos.le
    have hW : (coneSpace S o).OnSeg (ray S o pa σ) (ray S o pb σ)
        (M (J S o pa pb z) (J S o pa pb z')) ((mid z z').2 / σ) := by
      apply (coneSpace S o).onSeg_of_le
      · show ρ _ _ ≤ _ * ρ _ _
        have c := (coneSpace S o).d_comm (ray S o pa σ) (M (J S o pa pb z) (J S o pa pb z'))
        simp only [coneSpace_d] at c
        rw [c, hf]
        have : (mid z z').2 / σ * (σ * delta S o pa pb) = (z.2 + z'.2) / 2 * delta S o pa pb := by
          simp only [mid]; field_simp
        rw [this]; exact wX
      · show ρ _ _ ≤ _ * ρ _ _
        rw [hf]
        have : (1 - (mid z z').2 / σ) * (σ * delta S o pa pb) = (z.1 + z'.1) / 2 * delta S o pa pb := by
          simp only [mid]; field_simp; rw [hσdef, hs, hs']; ring
        rw [this]; exact wY
    have hJ := J_onSeg S o pa pb hmQ (s := σ) (by rw [hσ])
    have hτ0 : 0 ≤ (mid z z').2 / σ := div_nonneg hmQ.2 hσpos.le
    have hτ1 : (mid z z').2 / σ ≤ 1 := by
      rw [div_le_one hσpos, ← hσ]; linarith [hmQ.1]
    exact (coneSpace S o).onSeg_unique hτ0 hτ1 hW hJ
  · have h1 : z = 0 := Prod.ext (by simp; linarith [hz.1, hz.2, hz'.1, hz'.2])
      (by simp; linarith [hz.1, hz.2, hz'.1, hz'.2])
    have h2 : z' = 0 := Prod.ext (by simp; linarith [hz.1, hz.2, hz'.1, hz'.2])
      (by simp; linarith [hz.1, hz.2, hz'.1, hz'.2])
    subst h1 h2
    have : mid (0 : ℝ × ℝ) 0 = 0 := by ext <;> simp [mid]
    rw [this]
    exact (coneSpace S o).ax3 _

/-- The pull-back distance on the quadrant. -/
def Nf (z z' : ℝ × ℝ) : ℝ := ρ (J S o pa pb z) (J S o pa pb z')

lemma Nf_mid {z1 z2 z3 z4 : ℝ × ℝ} (h1 : InQ z1) (h2 : InQ z2) (h3 : InQ z3) (h4 : InQ z4) :
    Nf S o pa pb (mid z1 z2) (mid z3 z4) =
      ρ (M (J S o pa pb z1) (J S o pa pb z2)) (M (J S o pa pb z3) (J S o pa pb z4)) := by
  have e1 := (coneSpace S o).d_zero_symm (J_mid S o pa pb h1 h2)
  have e2 := (coneSpace S o).d_zero_symm (J_mid S o pa pb h3 h4)
  exact (coneSpace S o).d_congr e1 e2

lemma J_zero_ray : ρ (J S o pa pb 0) (ray S o pa 0) = 0 := by
  have := J_left S o pa pb (z := 0) ⟨le_rfl, le_rfl⟩
  simp only [Prod.fst_zero, Prod.snd_zero, add_zero, zero_mul] at this
  have c := (coneSpace S o).d_comm (ray S o pa 0) (J S o pa pb 0)
  simp only [coneSpace_d] at c
  rw [← c]; exact this

lemma Nf_bound {z : ℝ × ℝ} (hz : InQ z) :
    Nf S o pa pb 0 z ≤ (S.d o pa + delta S o pa pb) * (z.1 + z.2) := by
  have hs := add_nonneg hz.1 hz.2
  have t1 := (coneSpace S o).d_tri (J S o pa pb 0) (ray S o pa 0) (J S o pa pb z)
  have t2 := (coneSpace S o).d_tri (ray S o pa 0) (ray S o pa (z.1 + z.2)) (J S o pa pb z)
  simp only [coneSpace_d] at t1 t2
  rw [J_zero_ray, J_left S o pa pb hz, ρ_ray_ray S o pa le_rfl hs, zero_sub, abs_neg,
    abs_of_nonneg hs] at *
  have hd := delta_nonneg S o pa pb
  have hz2 := hz.2
  have hz1 := hz.1
  simp only [Nf]
  nlinarith [S.d_nonneg o pa]

/-- `N` satisfies the hypotheses of the quadrant lemma. -/
lemma qhyp : QHyp (Nf S o pa pb) (S.d o pa + delta S o pa pb) where
  self z _ := (coneSpace S o).d_self _
  comm z w _ _ := (coneSpace S o).d_comm _ _
  tri x y z _ _ _ := (coneSpace S o).d_tri _ _ _
  bus z1 z2 z3 z4 h1 h2 h3 h4 := by
    rw [Nf_mid S o pa pb h1 h2 h3 h4]
    exact (coneSpace S o).bus _ _ _ _
  quad z1 z2 z3 z4 h1 h2 h3 h4 := by
    rw [Nf_mid S o pa pb h1 h2 h3 h4, Nf_mid S o pa pb h1 h4 h3 h2]
    exact (coneSpace S o).quad _ _ _ _
  bound z hz := by
    have := Nf_bound S o pa pb hz
    linarith

/-! ## Boundary values and the Fermat inequality in the plane -/

lemma J_e1 {s : ℝ} (hs : 0 ≤ s) : ρ (J S o pa pb (s, 0)) (ray S o pa s) = 0 := by
  have := J_left S o pa pb (z := (s, 0)) ⟨hs, le_rfl⟩
  simp only [add_zero, zero_mul] at this
  have c := (coneSpace S o).d_comm (ray S o pa s) (J S o pa pb (s, 0))
  simp only [coneSpace_d] at c
  rw [← c]; exact this

lemma J_e2 {s : ℝ} (hs : 0 ≤ s) : ρ (J S o pa pb (0, s)) (ray S o pb s) = 0 := by
  have := J_right S o pa pb (z := (0, s)) ⟨le_rfl, hs⟩
  simp only [zero_add, zero_mul] at this
  exact this

lemma ray_zero_O (p : X) : ρ (ray S o p 0) (O S o) = 0 := by
  have := ρ_O_ray S o p (le_refl (0 : ℝ))
  rw [zero_mul] at this
  have c := (coneSpace S o).d_comm (ray S o p 0) (O S o)
  simp only [coneSpace_d] at c
  rw [c]; exact this

lemma J_zero_O : ρ (J S o pa pb 0) (O S o) = 0 :=
  (coneSpace S o).d_zero_trans (J_zero_ray S o pa pb) (ray_zero_O S o pa)

lemma Nf_e1 : Nf S o pa pb 0 (1, 0) = S.d o pa := by
  have e := (coneSpace S o).d_congr (J_zero_O S o pa pb) (J_e1 S o pa pb (zero_le_one' ℝ))
  simp only [coneSpace_d] at e
  rw [Nf, e, ρ_O_ray S o pa zero_le_one, one_mul]

lemma Nf_e2 : Nf S o pa pb 0 (0, 1) = S.d o pb := by
  have e := (coneSpace S o).d_congr (J_zero_O S o pa pb) (J_e2 S o pa pb (zero_le_one' ℝ))
  simp only [coneSpace_d] at e
  rw [Nf, e, ρ_O_ray S o pb zero_le_one, one_mul]

lemma Nf_e21 : Nf S o pa pb (0, 1) (1, 0) = delta S o pa pb := by
  have e := (coneSpace S o).d_congr (J_e2 S o pa pb (zero_le_one' ℝ))
    (J_e1 S o pa pb (zero_le_one' ℝ))
  simp only [coneSpace_d] at e
  have c := (coneSpace S o).d_comm (ray S o pb 1) (ray S o pa 1)
  simp only [coneSpace_d] at c
  rw [Nf, e, c, f_eq S o pa pb zero_le_one, one_mul]

lemma Nf_fermat (pc : X)
    (hmin : ∀ q, S.d o pa + S.d o pb + S.d o pc ≤ S.d q pa + S.d q pb + S.d q pc)
    (z : ℝ × ℝ) (K : ℕ) :
    2 ^ K * (S.d o pa + S.d o pb) ≤
      Nf S o pa pb z (2 ^ K, 0) + Nf S o pa pb z (0, 2 ^ K) + Nf S o pa pb z 0 := by
  have h := fermat_cone S o pa pb pc hmin (J S o pa pb z) K
  have e1 := (coneSpace S o).d_congr_right (J S o pa pb z) (J_e1 S o pa pb (s := 2 ^ K) (by positivity))
  have e2 := (coneSpace S o).d_congr_right (J S o pa pb z) (J_e2 S o pa pb (s := 2 ^ K) (by positivity))
  have e3 := (coneSpace S o).d_congr_right (J S o pa pb z) (J_zero_O S o pa pb)
  simp only [coneSpace_d] at e1 e2 e3
  simp only [Nf]
  rw [e1, e2, e3]
  exact h

end two

end OM.NNN30.Geom
