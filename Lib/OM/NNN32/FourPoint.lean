import Lib.OM.NNN32.SquareTest
import PLATFORM.Statements.«R113.19»

/-! # Degenerate sectors and the four-point inequality

At a point on a segment the directions to its endpoints are opposite. If an off-segment
point branches strictly toward both endpoints its unit direction in the cone would
coincide with both. Thus distance to that point along the segment is the maximum of
the two affine lower bounds from the endpoints. Dyadic approximation at their
intersection gives the four-point inequality without a completeness assumption.
-/

noncomputable section

namespace OM.NNN32

open OM.NNN30.Geom ConePt Filter Topology

variable {X : Type*} (S : MidSpace X)

/-- Every pair of nontrivial directions spans a sector of zero area. -/
def degenerateSectors : Prop :=
  ∀ o p q : X, 0 < S.d o p →
    4*(S.d o p)^2*(S.d o q)^2-((S.d o p)^2+(S.d o q)^2-(delta S o p q)^2)^2 ≤ 0

private def unitRay (o p : X) := ray S o p (1 / S.d o p)

private lemma unitRay_sq (o p q : X) (hp : 0 < S.d o p) (hq : 0 < S.d o q) :
    S.d o p * S.d o q * ρ (unitRay S o p) (unitRay S o q)^2 =
      delta S o p q^2 - (S.d o p - S.d o q)^2 := by
  have a : InQ ((1/S.d o p,0) : ℝ × ℝ) := ⟨by positivity,le_rfl⟩
  have b : InQ ((0,1/S.d o q) : ℝ × ℝ) := ⟨le_rfl,by positivity⟩
  have h := (qhyp S o p q).formula a b
  rw [Nf_e1,Nf_e2,Nf_e21] at h
  have e := (coneSpace S o).d_congr (J_e1 S o p q a.1) (J_e2 S o p q b.2)
  change Nf S o p q _ _ = ρ (unitRay S o p) (unitRay S o q) at e
  rw [← e,h]
  dsimp
  field_simp
  ring

private lemma unitRay_zero (h : degenerateSectors S)
    {o p q : X} (hp : 0 < S.d o p) (hq : 0 < S.d o q) (hlt : S.d p q < S.d o p + S.d o q) :
    ρ (unitRay S o p) (unitRay S o q) = 0 := by
  let a := S.d o p
  let b := S.d o q
  let δ := delta S o p q
  let k := a^2+b^2-δ^2
  have hd : 4*a^2*b^2-k^2 ≤ 0 := h o p q hp
  have hδ : δ < a+b := (delta_le S o p q).trans_lt hlt
  have hδ0 : 0 ≤ δ := delta_nonneg _ _ _ _
  have hlow : 0 < 2*a*b+k := by
    have hsq := (pow_lt_pow_left₀ hδ hδ0 (by decide +kernel : 2 ≠ 0))
    dsimp [k]; linarith
  have hhigh : 2*a*b ≤ k := by
    by_contra! hn
    nlinarith only [mul_pos (sub_pos.2 hn) hlow,hd]
  have hunit := unitRay_sq S o p q hp hq
  change a*b*_ = δ^2-(a-b)^2 at hunit
  have hle : a*b*ρ (unitRay S o p) (unitRay S o q)^2 ≤ 0 := by
    rw [hunit]; dsimp [k] at hhigh; linarith
  by_contra hn
  exact (not_lt_of_ge hle) (mul_pos (mul_pos hp hq) (sq_pos_of_ne_zero hn))

private lemma delta_of_between (o p q : X) (h : S.d p q = S.d o p + S.d o q) :
    delta S o p q = S.d o p + S.d o q := by
  apply le_antisymm ((delta_le _ _ _ _).trans_eq h)
  apply le_ciInf
  intro n
  have t1 := S.d_tri p (hx S o p n) q
  have t2 := S.d_tri (hx S o p n) (hx S o q n) q
  rw [h,S.d_comm p _,hx_right] at t1
  rw [hx_right] at t2
  let z := (2:ℝ)^n
  have hz : 0 < z := by positivity
  have hdist : (S.d o p + S.d o q)/z ≤ S.d (hx S o p n) (hx S o q n) := by
    dsimp [z]; simp only [div_eq_mul_inv, one_mul] at *; linarith only [t1,t2]
  exact ((div_le_iff₀ hz).1 hdist).trans_eq (mul_comm _ _)

private lemma segment_distance (h : degenerateSectors S)
    (o a b c : X) (hseg : S.d a c = S.d o a + S.d o c) :
    S.d o b = max (S.d a b - S.d o a) (S.d c b - S.d o c) := by
  have lower (z : X) : S.d z b - S.d o z ≤ S.d o b := by
    have t := S.d_tri z o b
    rw [S.d_comm z o] at t
    linarith
  apply le_antisymm _ (max_le (lower a) (lower c))
  by_contra! hn
  have h1 := (max_lt_iff.1 hn).1
  have h2 := (max_lt_iff.1 hn).2
  have ha : 0 < S.d o a := by
    rcases (S.d_nonneg o a).eq_or_lt with hz | hz
    · rw [S.d_congr_left hz.symm b] at h1
      linarith
    · exact hz
  have hc' : 0 < S.d o c := by
    rcases (S.d_nonneg o c).eq_or_lt with hz | hz
    · rw [S.d_congr_left hz.symm b] at h2
      linarith
    · exact hz
  have hb : 0 < S.d o b := by
    rcases (S.d_nonneg o b).eq_or_lt with hz | hz
    · rw [← S.d_congr_right a hz.symm,S.d_comm a o] at h1
      linarith
    · exact hz
  have e1 := unitRay_zero S h ha hb (by linarith : S.d a b < _)
  have e2 := unitRay_zero S h hb hc' (by linarith [S.d_comm b c] : S.d b c < _)
  have both := (coneSpace S o).d_zero_trans e1 e2
  change ρ (unitRay S o a) (unitRay S o c) = 0 at both
  have hunit := unitRay_sq S o a c ha hc'
  rw [both,delta_of_between S o a c hseg] at hunit
  nlinarith [mul_pos ha hc']

/-- A midpoint space in which all sectors are degenerate satisfies the tree four-point inequality. -/
theorem fourPoint_of_degenerate (h : degenerateSectors S) (a b c e : X) :
    S.d a c + S.d b e ≤ max (S.d a b + S.d c e) (S.d a e + S.d b c) := by
  let l := S.d a c
  rcases (S.d_nonneg a c).eq_or_lt with hz | hl
  · rw [← hz,zero_add]
    have t := S.d_tri b a e
    rw [S.d_comm b a,S.d_congr_left hz.symm e] at t
    exact t.trans (le_max_left _ _)
  let u := (l+S.d a b-S.d c b)/2
  have t1 := S.d_tri c a b
  rw [S.d_comm c a] at t1
  have t2 := S.d_tri a c b
  have hu : 0 ≤ u := by dsimp [u,l]; linarith
  have hul : u ≤ l := by dsimp [u,l]; linarith
  let t := u/l
  have ht : 0 ≤ t := div_nonneg hu hl.le
  have ht1 : t ≤ 1 := (div_le_one hl).2 hul
  let U (x : ℝ) (z : X) := max (S.d a z - x*l) (S.d c z - (1-x)*l)
  have hU (z : X) : Continuous (fun x => U x z) := by unfold U; fun_prop
  have hbnd (n : ℕ) :
      S.d b e ≤ U ((frac t n : ℝ)/2^n) b + U ((frac t n : ℝ)/2^n) e := by
    let o := S.geo a c n (frac t n)
    have hleft := S.geo_left n a c (frac_le t n)
    rw [S.d_comm a _] at hleft
    have hright := S.geo_right n a c (frac_le t n)
    have hseg : S.d a c = S.d o a + S.d o c := by rw [hleft,hright]; ring
    have dist (z : X) : S.d o z = U ((frac t n : ℝ)/2^n) z := by
      rw [segment_distance S h o a z c hseg,hleft,hright]
    have tri := S.d_tri b o e
    rwa [S.d_comm b o,dist,dist] at tri
  have hlim := ((hU b).tendsto t).comp (tendsto_frac ht ht1)
  have hb := ge_of_tendsto (hlim.add (((hU e).tendsto t).comp (tendsto_frac ht ht1)))
    (Eventually.of_forall hbnd)
  change S.d b e ≤ U t b + U t e at hb
  have htl : t*l = u := div_mul_cancel₀ _ hl.ne'
  have hel : (1-t)*l = l-u := by rw [sub_mul,one_mul,htl]
  unfold U at hb
  rw [htl,hel] at hb
  have heq : S.d c b-(l-u) = S.d a b-u := by dsimp [u]; ring
  rw [heq,max_self] at hb
  change l + S.d b e ≤ _
  rw [S.d_comm b c]
  rcases le_total (S.d a e-u) (S.d c e-(l-u)) with hle | hle
  · rw [max_eq_right hle] at hb
    exact (by linarith : l+S.d b e ≤ S.d a b + S.d c e).trans (le_max_left _ _)
  · rw [max_eq_left hle] at hb
    exact (by dsimp [u] at hb; linarith : l+S.d b e ≤ S.d a e+S.d c b).trans (le_max_right _ _)

theorem proof_R113_19 : S_R113_19 := by
  intro X S κ hk hκ h
  exact fourPoint_of_degenerate S (det_nonpos_of_twoTerm hk hκ h)

end OM.NNN32
