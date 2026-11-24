import Lib.OM.NNN30.Geom.Plane
import Mathlib.Tactic.LinearCombination

/-! # First variation for a weighted sum of three distances -/

noncomputable section
namespace OM.NNN36

open Filter Topology NNN30.Geom NNN30.Geom.ConePt

variable {X : Type*}

private theorem weighted_fermat_cone (S : MidSpace X) (o p q r : X) {u v w : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hmin : ∀ x, u*S.d o p + v*S.d o q + w*S.d o r ≤ u*S.d x p + v*S.d x q + w*S.d x r)
    (Q : ConePt S o) (K : ℕ) :
    2^K * (u * S.d o p + v * S.d o q) ≤
      u * ρ Q (ray S o p (2^K)) + v * ρ Q (ray S o q (2^K)) + w * ρ Q (O S o) := by
  refine le_of_tendsto_of_tendsto tendsto_const_nhds
    ((((tendsto_ρ _ _).const_mul u).add ((tendsto_ρ _ _).const_mul v)).add
      ((tendsto_ρ _ _).const_mul w)) ?_
  filter_upwards [eventually_U K (fun n hn => hn)] with n hn
  simp only [sd, O]
  rw [ray_pow_seq S o p K hn, ray_pow_seq S o q K hn]
  have h₁ := S.d_tri (Q.seq n) (hx S o p (n-K)) p
  have h₂ := S.d_tri (Q.seq n) (hx S o q (n-K)) q
  rw [hx_right] at h₁ h₂
  have h₃ := S.d_tri (Q.seq n) o r
  have hcost := add_le_add (add_le_add (mul_le_mul_of_nonneg_left h₁ hu)
      (mul_le_mul_of_nonneg_left h₂ hv)) (mul_le_mul_of_nonneg_left h₃ hw)
  let bill := u*S.d (Q.seq n) (hx S o p (n-K)) + v*S.d (Q.seq n) (hx S o q (n-K)) +
    w*S.d (Q.seq n) o
  have hscaled : (u*S.d o p + v*S.d o q) / 2^(n-K) ≤ bill := by
    dsimp only [bill]
    have h := (hmin (Q.seq n)).trans hcost
    rw [div_eq_mul_inv]
    simp only [one_div] at h
    linear_combination h
  rw [div_le_iff₀ (by positivity)] at hscaled
  have hpow : (2 : ℝ)^n = 2^K * 2^(n-K) := by rw [← pow_add, Nat.add_sub_cancel' hn]
  exact (mul_le_mul_of_nonneg_left hscaled (by positivity : 0 ≤ (2 : ℝ)^K)).trans_eq (by
    dsimp only [bill]; rw [hpow]; ring)

private theorem weighted_fermat_plane (S : MidSpace X) (o p q r : X) {u v w : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hmin : ∀ x, u*S.d o p + v*S.d o q + w*S.d o r ≤ u*S.d x p + v*S.d x q + w*S.d x r)
    (z : ℝ × ℝ) (K : ℕ) :
    2^K * (u * S.d o p + v * S.d o q) ≤
      u * Nf S o p q z (2^K,0) + v * Nf S o p q z (0,2^K) + w * Nf S o p q z 0 := by
  have h := weighted_fermat_cone S o p q r hu hv hw hmin (J S o p q z) K
  have e₁ := (coneSpace S o).d_congr_right (J S o p q z) (J_e1 S o p q (s := 2^K) (by positivity))
  have e₂ := (coneSpace S o).d_congr_right (J S o p q z) (J_e2 S o p q (s := 2^K) (by positivity))
  have e₃ := (coneSpace S o).d_congr_right (J S o p q z) (J_zero_O S o p q)
  simpa only [Nf, coneSpace_d] using h.trans_eq (by
    simp only [coneSpace_d] at e₁ e₂ e₃; rw [← e₁, ← e₂, ← e₃])

/-- The error when linearizing a distance at radius `l` is bounded by a term
proportional to `1/l`. This follows by dropping the square of the distance change. -/
private theorem distance_remainder {p q l d : ℝ} (hl : 0 < l)
    (he : q^2 = l^2 - 2*l*d + p^2) : q - l + d ≤ p^2 / (2*l) := by
  apply (le_div_iff₀ (by positivity)).2
  nlinarith only [he, sq_nonneg (q-l)]

private theorem weighted_plane_angle {N : ℝ × ℝ → ℝ × ℝ → ℝ} {L a b δ u v w : ℝ}
    (hq : QHyp N L) (ha : 0 < a) (hb : 0 < b)
    (hu : 0 < u) (hv : 0 < v) (hw : 0 ≤ w)
    (h₁ : N 0 (1,0) = a) (h₂ : N 0 (0,1) = b) (h₃ : N (0,1) (1,0) = δ)
    (hmin : ∀ z K, (2 : ℝ)^(K : ℕ) * (u*a + v*b) ≤
      u*N z (2^K,0) + v*N z (0,2^K) + w*N z 0) :
    (a^2 + b^2 - δ^2) * (u*v) ≤ a*b*(w^2-u^2-v^2) := by
  let z : ℝ × ℝ := (u/a, v/b)
  let e := (a^2+b^2-δ^2)/(a*b)
  let s := u + e*v/2
  let t := v + e*u/2
  let p := N z 0
  have hz : InQ z := ⟨div_nonneg hu.le ha.le, div_nonneg hv.le hb.le⟩
  have hzero : InQ (0 : ℝ × ℝ) := ⟨le_rfl,le_rfl⟩
  have hp : 0 ≤ p := hq.nonneg hz hzero
  have form (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
      N z (x,y)^2 = (a*x-u)^2 + (a*x-u)*(b*y-v)*e + (b*y-v)^2 := by
    rw [hq.formula hz (show InQ (x,y) from ⟨hx,hy⟩), h₁, h₂, h₃]
    dsimp [z,e]
    field_simp
  have hp₂ : p^2 = u^2 + e*u*v + v^2 := by
    calc p^2 = _ := form 0 0 le_rfl le_rfl
         _ = _ := by ring
  have hdot : u*s+v*t = p^2 := by rw [hp₂]; dsimp [s,t]; ring
  have hpw : p^2 ≤ w*p := by
    by_contra! hgap
    let C := p^2 * (u/(2*a) + v/(2*b))
    obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (C/(p^2-w*p)) (by norm_num : (1 : ℝ) < 2)
    let R : ℝ := 2^K
    have hR : 0 < R := by dsimp [R]; positivity
    have hA : N z (R,0)^2 = (R*a)^2 - 2*(R*a)*s + p^2 := by
      rw [form _ _ hR.le le_rfl, hp₂]; dsimp [s]; ring
    have hB : N z (0,R)^2 = (R*b)^2 - 2*(R*b)*t + p^2 := by
      rw [form _ _ le_rfl hR.le, hp₂]; dsimp [t]; ring
    have hrem := add_le_add (mul_le_mul_of_nonneg_left (distance_remainder (mul_pos hR ha) hA) hu.le)
      (mul_le_mul_of_nonneg_left (distance_remainder (mul_pos hR hb) hB) hv.le)
    have hbnd : u*(p^2/(2*(R*a))) + v*(p^2/(2*(R*b))) = C/R := by
      dsimp only [C]; field_simp
    rw [hbnd] at hrem
    have hF : R*(u*a+v*b) ≤ u * N z (R,0) + v * N z (0,R) + w*p := hmin z K
    have hle : p^2-w*p ≤ C/R := by linarith only [hF, hdot, hrem]
    rw [le_div_iff₀ hR] at hle
    exact ((div_lt_iff₀ (sub_pos.mpr hgap)).mp hK).not_ge
      (by simpa only [R, mul_comm (p^2-w*p)] using hle)
  have hp_le : p ≤ w := by nlinarith only [hpw, hp, hw, sq_nonneg (p-w)]
  have he := hp₂.symm.trans_le (pow_le_pow_left₀ hp hp_le 2)
  dsimp only [e] at he
  field_simp at he
  nlinarith only [he]

/-- Weighted analogue of the pairwise angle condition at a minimizing site.
The polynomial form also covers zero distances to a terminal. -/
theorem weighted_angle (S : MidSpace X) (o p q r : X) {u v w : ℝ}
    (hu : 0 < u) (hv : 0 < v) (hw : 0 ≤ w)
    (hmin : ∀ x, u*S.d o p + v*S.d o q + w*S.d o r ≤ u*S.d x p + v*S.d x q + w*S.d x r) :
    (S.d o p ^ 2 + S.d o q ^ 2 - S.d p q ^ 2) * (u*v) ≤
      S.d o p * S.d o q * (w^2-u^2-v^2) := by
  rcases (S.d_nonneg o p).lt_or_eq with ha | ha
  · rcases (S.d_nonneg o q).lt_or_eq with hb | hb
    · have h := weighted_plane_angle (qhyp S o p q) ha hb hu hv hw
        (Nf_e1 S o p q) (Nf_e2 S o p q) (Nf_e21 S o p q)
        (weighted_fermat_plane S o p q r hu.le hv.le hw hmin)
      have hd := pow_le_pow_left₀ (delta_nonneg S o p q) (delta_le S o p q) 2
      exact (mul_le_mul_of_nonneg_right (sub_le_sub_left hd _) (mul_nonneg hu.le hv.le)).trans h
    · have h := S.d_tri o q p
      rw [← hb, zero_add, S.d_comm q p] at h
      rw [← hb]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        add_zero, mul_zero, zero_mul]
      exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (pow_le_pow_left₀ ha.le h 2)) (by positivity)
  · have h := S.d_tri o p q
    rw [← ha, zero_add] at h
    rw [← ha]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      zero_add, zero_mul]
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (pow_le_pow_left₀ (S.d_nonneg o q) h 2))
      (by positivity)

end OM.NNN36

