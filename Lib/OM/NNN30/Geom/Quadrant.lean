import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Analysis.SpecificLimits.Basic

/-! # The quadrant lemma

Let `N` be a function on pairs of points of the closed quadrant `[0,∞)²` which is a pseudometric
there, satisfies the midpoint Busemann inequality
`N(mid z1 z2, mid z3 z4) ≤ (N z1 z3 + N z2 z4) / 2`, the quadrilateral inequality (10) for affine
midpoints, and the bound `N 0 z ≤ L (z.1 + z.2)`.  Then (`formula`)
`N z z' ^ 2 = Φ (z' - z)` for all `z, z'` in the quadrant, where `Φ` is the quadratic form with
`Φ e1 = N 0 e1 ^ 2`, `Φ e2 = N 0 e2 ^ 2`, `Φ (e1 - e2) = N e2 e1 ^ 2`.

Midpoint Busemann gives dyadic Busemann convexity and dyadic
constant speed; with a point `w` near an interior point `y` this gives
`N y (y + v) ≤ N z (z + v)` (`cmp`), hence translation invariance; the common value `P v` is even,
subadditive, dyadically homogeneous and Lipschitz; (10) gives the parallelogram law for `P²` and
its reverse by substitution; `B v w = (P(v+w)² - P(v-w)²)/4` is then additive (Jordan–von Neumann)
and, being continuous, `ℝ`-linear (`map_real_smul`).  No compactness or limit of `N` is needed
beyond the dyadic limits `C / 2^k → 0`. -/

noncomputable section

open Filter Topology

namespace OM.NNN30.Geom

/-- The closed quadrant `[0, ∞)²`. -/
def InQ (z : ℝ × ℝ) : Prop := 0 ≤ z.1 ∧ 0 ≤ z.2

/-- Affine midpoint in the plane. -/
def mid (z w : ℝ × ℝ) : ℝ × ℝ := ((z.1 + w.1) / 2, (z.2 + w.2) / 2)

lemma le_of_le_add_div_pow {x y C : ℝ} (h : ∀ k : ℕ, x ≤ y + C / 2 ^ k) : x ≤ y := by
  have hlim : Tendsto (fun k : ℕ => y + C / 2 ^ k) atTop (𝓝 (y + 0)) := by
    refine tendsto_const_nhds.add ?_
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).const_mul C
    rw [mul_zero] at this
    refine this.congr (fun k => ?_)
    rw [one_div_pow]; ring
  rw [add_zero] at hlim
  exact ge_of_tendsto' hlim h

/-- Hypotheses of the quadrant lemma. -/
structure QHyp (N : ℝ × ℝ → ℝ × ℝ → ℝ) (L : ℝ) : Prop where
  self : ∀ z, InQ z → N z z = 0
  comm : ∀ z w, InQ z → InQ w → N z w = N w z
  tri : ∀ x y z, InQ x → InQ y → InQ z → N x z ≤ N x y + N y z
  bus : ∀ z1 z2 z3 z4, InQ z1 → InQ z2 → InQ z3 → InQ z4 →
    N (mid z1 z2) (mid z3 z4) ≤ (N z1 z3 + N z2 z4) / 2
  quad : ∀ z1 z2 z3 z4, InQ z1 → InQ z2 → InQ z3 → InQ z4 →
    N (mid z1 z2) (mid z3 z4) ^ 2 + N (mid z1 z4) (mid z3 z2) ^ 2 ≤
      (N z1 z3 ^ 2 + N z2 z4 ^ 2) / 2
  bound : ∀ z, InQ z → N 0 z ≤ L * (z.1 + z.2)

namespace QHyp

variable {N : ℝ × ℝ → ℝ × ℝ → ℝ} {L : ℝ} (h : QHyp N L)
include h

lemma nonneg {z w : ℝ × ℝ} (hz : InQ z) (hw : InQ w) : 0 ≤ N z w := by
  have := h.tri z w z hz hw hz
  rw [h.self z hz, h.comm w z hw hz] at this
  linarith

omit h in
lemma inQ_mid {z w : ℝ × ℝ} (hz : InQ z) (hw : InQ w) : InQ (mid z w) := by
  constructor <;> simp only [mid] <;> linarith [hz.1, hz.2, hw.1, hw.2]

omit h in
lemma inQ_seg {y v : ℝ × ℝ} {t : ℝ} (hy : InQ y) (hyv : InQ (y + v)) (t0 : 0 ≤ t) (t1 : t ≤ 1) :
    InQ (y + t • v) := by
  obtain ⟨h1, h2⟩ := hy
  obtain ⟨h3, h4⟩ := hyv
  simp only [Prod.fst_add, Prod.snd_add] at h3 h4
  constructor <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  · nlinarith
  · nlinarith

omit h in
lemma inQ_comb {z w : ℝ × ℝ} {t : ℝ} (hz : InQ z) (hw : InQ w) (t0 : 0 ≤ t) (t1 : t ≤ 1) :
    InQ (t • z + (1 - t) • w) := by
  obtain ⟨h1, h2⟩ := hz
  obtain ⟨h3, h4⟩ := hw
  have t2 : 0 ≤ 1 - t := by linarith
  constructor <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  · positivity
  · positivity

omit h in
lemma mid_self (z : ℝ × ℝ) : mid z z = z := by
  ext <;> simp [mid]

/-- Dyadic constant speed, one step. -/
lemma half {z w : ℝ × ℝ} (hz : InQ z) (hw : InQ w) : N z (mid z w) = N z w / 2 := by
  have hm := inQ_mid hz hw
  have h1 : N z (mid z w) ≤ N z w / 2 := by
    have := h.bus z z z w hz hz hz hw
    rw [mid_self, h.self z hz] at this
    linarith
  have h2 : N (mid z w) w ≤ N z w / 2 := by
    have := h.bus z w w w hz hw hw hw
    rw [mid_self, h.self w hw] at this
    linarith
  have := h.tri z (mid z w) w hz hm hw
  linarith

/-- Dyadic constant speed. -/
lemma dcs {y v : ℝ × ℝ} (hy : InQ y) (hyv : InQ (y + v)) (k : ℕ) :
    N y (y + (1 / 2 ^ k : ℝ) • v) = N y (y + v) / 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk : InQ (y + (1 / 2 ^ k : ℝ) • v) :=
      inQ_seg hy hyv (by positivity) (by rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num))
    have e : y + (1 / 2 ^ (k + 1) : ℝ) • v = mid y (y + (1 / 2 ^ k : ℝ) • v) := by
      ext <;> simp [mid] <;> ring
    rw [e, h.half hy hk, ih]
    ring

/-- Dyadic Busemann convexity. -/
lemma db (k : ℕ) {z1 z2 z3 z4 : ℝ × ℝ} (h1 : InQ z1) (h2 : InQ z2) (h3 : InQ z3) (h4 : InQ z4) :
    N ((1 / 2 ^ k : ℝ) • z1 + (1 - 1 / 2 ^ k : ℝ) • z2) ((1 / 2 ^ k : ℝ) • z3 + (1 - 1 / 2 ^ k : ℝ) • z4)
      ≤ 1 / 2 ^ k * N z1 z3 + (1 - 1 / 2 ^ k) * N z2 z4 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have t0 : (0 : ℝ) ≤ 1 / 2 ^ k := by positivity
    have t1 : (1 / 2 ^ k : ℝ) ≤ 1 := by
      rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
    have hA := inQ_comb h1 h2 t0 t1
    have hB := inQ_comb h3 h4 t0 t1
    have e1 : (1 / 2 ^ (k + 1) : ℝ) • z1 + (1 - 1 / 2 ^ (k + 1) : ℝ) • z2 =
        mid ((1 / 2 ^ k : ℝ) • z1 + (1 - 1 / 2 ^ k : ℝ) • z2) z2 := by
      ext <;> simp [mid] <;> ring
    have e2 : (1 / 2 ^ (k + 1) : ℝ) • z3 + (1 - 1 / 2 ^ (k + 1) : ℝ) • z4 =
        mid ((1 / 2 ^ k : ℝ) • z3 + (1 - 1 / 2 ^ k : ℝ) • z4) z4 := by
      ext <;> simp [mid] <;> ring
    rw [e1, e2]
    have := h.bus _ z2 _ z4 hA h2 hB h4
    have e3 : (1 / 2 ^ (k + 1) : ℝ) = 1 / 2 ^ k / 2 := by ring
    rw [e3]
    linarith

/-- Comparison: an interior base point has the least displacement length. -/
lemma cmp {y z v : ℝ × ℝ} (hy1 : 0 < y.1) (hy2 : 0 < y.2) (hz : InQ z) (hzv : InQ (z + v))
    (hyv : InQ (y + v)) : N y (y + v) ≤ N z (z + v) := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (2 + z.1 / y.1 + z.2 / y.2) (by norm_num : (1 : ℝ) < 2)
  have hz1 := hz.1
  have hz2 := hz.2
  have hq1 : 0 ≤ z.1 / y.1 := by positivity
  have hq2 : 0 ≤ z.2 / y.2 := by positivity
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  set ε : ℝ := 1 / 2 ^ k with hε
  have hε0 : 0 < ε := by positivity
  have hε2 : ε < 1 / 2 := by
    rw [hε, div_lt_div_iff₀ h2k (by norm_num)]; linarith
  have hεz1 : ε * z.1 ≤ y.1 := by
    have : z.1 / y.1 < 2 ^ k := by linarith
    rw [div_lt_iff₀ hy1] at this
    rw [hε, div_mul_eq_mul_div, one_mul, div_le_iff₀ h2k]; linarith
  have hεz2 : ε * z.2 ≤ y.2 := by
    have : z.2 / y.2 < 2 ^ k := by linarith
    rw [div_lt_iff₀ hy2] at this
    rw [hε, div_mul_eq_mul_div, one_mul, div_le_iff₀ h2k]; linarith
  have h1ε : 0 < 1 - ε := by linarith
  set w : ℝ × ℝ := (1 / (1 - ε)) • (y - ε • z) with hw
  have hinv : 0 ≤ 1 / (1 - ε) := one_div_nonneg.2 h1ε.le
  have hwQ : InQ w := by
    constructor <;> simp only [hw, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub, Prod.snd_sub,
      smul_eq_mul] <;> apply mul_nonneg hinv <;> linarith
  have ey : y = ε • z + (1 - ε) • w := by
    rw [hw, smul_smul, mul_one_div_cancel h1ε.ne', one_smul]; abel
  have eyv : y + ε • v = ε • (z + v) + (1 - ε) • w := by
    rw [hw, smul_smul, mul_one_div_cancel h1ε.ne', one_smul, smul_add]; abel
  have hdb := h.db k hz hwQ hzv hwQ
  rw [← hε, ← ey, ← eyv, h.self w hwQ, mul_zero, add_zero] at hdb
  have hd := h.dcs ⟨hy1.le, hy2.le⟩ hyv k
  rw [← hε] at hd
  rw [hd] at hdb
  have h3 : N y (y + v) / 2 ^ k ≤ N z (z + v) / 2 ^ k := by
    calc N y (y + v) / 2 ^ k ≤ ε * N z (z + v) := hdb
      _ = N z (z + v) / 2 ^ k := by rw [hε]; ring
  exact (div_le_div_iff_of_pos_right h2k).1 h3

/-- The interior base point used to define `P`. -/
def cpt (v : ℝ × ℝ) : ℝ × ℝ := (1 + |v.1|, 1 + |v.2|)

/-- The displacement length `P v`. -/
def P (N : ℝ × ℝ → ℝ × ℝ → ℝ) (v : ℝ × ℝ) : ℝ := N (cpt v) (cpt v + v)

omit h in
lemma cpt_pos1 (v : ℝ × ℝ) : 0 < (cpt v).1 := by simp only [cpt]; positivity
omit h in
lemma cpt_pos2 (v : ℝ × ℝ) : 0 < (cpt v).2 := by simp only [cpt]; positivity
omit h in
lemma cpt_add (v : ℝ × ℝ) : InQ (cpt v + v) := by
  constructor <;> simp only [cpt, Prod.fst_add, Prod.snd_add]
  · have := neg_abs_le v.1; linarith
  · have := neg_abs_le v.2; linarith

/-- Translation invariance at interior base points. -/
lemma P_eq_int {y v : ℝ × ℝ} (hy1 : 0 < y.1) (hy2 : 0 < y.2) (hyv : InQ (y + v)) :
    N y (y + v) = P N v :=
  le_antisymm (h.cmp hy1 hy2 ⟨(cpt_pos1 v).le, (cpt_pos2 v).le⟩ (cpt_add v) hyv)
    (h.cmp (cpt_pos1 v) (cpt_pos2 v) ⟨hy1.le, hy2.le⟩ hyv (cpt_add v))

lemma P_zero : P N 0 = 0 := by
  rw [← h.P_eq_int (cpt_pos1 0) (cpt_pos2 0) (cpt_add 0), add_zero,
    h.self _ ⟨(cpt_pos1 0).le, (cpt_pos2 0).le⟩]

lemma P_half (v : ℝ × ℝ) (k : ℕ) : P N ((1 / 2 ^ k : ℝ) • v) = P N v / 2 ^ k := by
  have hy : InQ (cpt v) := ⟨(cpt_pos1 v).le, (cpt_pos2 v).le⟩
  have hk : InQ (cpt v + (1 / 2 ^ k : ℝ) • v) :=
    inQ_seg hy (cpt_add v) (by positivity)
      (by rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num))
  rw [← h.P_eq_int (cpt_pos1 v) (cpt_pos2 v) hk, h.dcs hy (cpt_add v) k]
  rfl

lemma P_add (v w : ℝ × ℝ) : P N (v + w) ≤ P N v + P N w := by
  set y : ℝ × ℝ := (1 + |v.1| + |w.1|, 1 + |v.2| + |w.2|) with hy
  have a1 := neg_abs_le v.1
  have a2 := neg_abs_le v.2
  have a3 := neg_abs_le w.1
  have a4 := neg_abs_le w.2
  have b1 := abs_nonneg v.1
  have b2 := abs_nonneg v.2
  have b3 := abs_nonneg w.1
  have b4 := abs_nonneg w.2
  have hy1 : 0 < y.1 := by simp only [hy]; linarith
  have hy2 : 0 < y.2 := by simp only [hy]; linarith
  have hyv1 : 0 < (y + v).1 := by simp only [hy, Prod.fst_add]; linarith
  have hyv2 : 0 < (y + v).2 := by simp only [hy, Prod.snd_add]; linarith
  have hyvw : InQ (y + v + w) := by
    constructor <;> simp only [hy, Prod.fst_add, Prod.snd_add] <;> linarith
  have hyvw' : InQ (y + (v + w)) := by rw [← add_assoc]; exact hyvw
  have t := h.tri y (y + v) (y + (v + w)) ⟨hy1.le, hy2.le⟩ ⟨hyv1.le, hyv2.le⟩ hyvw'
  rw [h.P_eq_int hy1 hy2 hyvw', h.P_eq_int hy1 hy2 ⟨hyv1.le, hyv2.le⟩, ← add_assoc,
    h.P_eq_int hyv1 hyv2 hyvw] at t
  exact t

lemma P_neg (v : ℝ × ℝ) : P N (-v) = P N v := by
  have a1 := neg_abs_le v.1
  have a2 := neg_abs_le v.2
  have c1 := le_abs_self v.1
  have c2 := le_abs_self v.2
  have hm1 : 0 < (cpt v + -v).1 := by simp only [cpt, Prod.fst_add, Prod.fst_neg]; linarith
  have hm2 : 0 < (cpt v + -v).2 := by simp only [cpt, Prod.snd_add, Prod.snd_neg]; linarith
  have e : cpt v + -v + v = cpt v := by abel
  have h1 := h.P_eq_int (cpt_pos1 v) (cpt_pos2 v) ⟨hm1.le, hm2.le⟩
  have h2 := h.P_eq_int hm1 hm2 (by rw [e]; exact ⟨(cpt_pos1 v).le, (cpt_pos2 v).le⟩)
  rw [e] at h2
  rw [← h1, h.comm _ _ ⟨(cpt_pos1 v).le, (cpt_pos2 v).le⟩ ⟨hm1.le, hm2.le⟩, h2]

lemma P_two (v : ℝ × ℝ) : P N ((2 : ℝ) • v) = 2 * P N v := by
  have := h.P_half ((2 : ℝ) • v) 1
  rw [smul_smul] at this
  norm_num at this
  linarith

lemma L_nonneg : 0 ≤ L := by
  have := h.bound (1, 1) ⟨by norm_num, by norm_num⟩
  have h0 := h.nonneg (z := 0) (w := (1, 1)) ⟨le_rfl, le_rfl⟩ ⟨by norm_num, by norm_num⟩
  norm_num at this
  linarith

lemma P_le (v : ℝ × ℝ) : P N v ≤ L * (|v.1| + |v.2|) := by
  have hL := h.L_nonneg
  refine le_of_le_add_div_pow (C := 4 * L) (fun k => ?_)
  have hk : (0 : ℝ) < 1 / 2 ^ k := by positivity
  set y : ℝ × ℝ := ((|v.1| - v.1) / 2 + 1 / 2 ^ k, (|v.2| - v.2) / 2 + 1 / 2 ^ k) with hy
  have c1 := le_abs_self v.1
  have c2 := le_abs_self v.2
  have a1 := neg_abs_le v.1
  have a2 := neg_abs_le v.2
  have hy1 : 0 < y.1 := by simp only [hy]; linarith
  have hy2 : 0 < y.2 := by simp only [hy]; linarith
  have hyv : InQ (y + v) := by
    constructor <;> simp only [hy, Prod.fst_add, Prod.snd_add] <;> linarith
  have h0 : InQ (0 : ℝ × ℝ) := ⟨le_rfl, le_rfl⟩
  have t := h.tri y 0 (y + v) ⟨hy1.le, hy2.le⟩ h0 hyv
  rw [h.P_eq_int hy1 hy2 hyv, h.comm y 0 ⟨hy1.le, hy2.le⟩ h0] at t
  have b1 := h.bound y ⟨hy1.le, hy2.le⟩
  have b2 := h.bound (y + v) hyv
  simp only [hy, Prod.fst_add, Prod.snd_add] at b1 b2
  have e : L * (|v.1| + |v.2|) + 4 * L / 2 ^ k =
      L * ((|v.1| - v.1) / 2 + 1 / 2 ^ k + ((|v.2| - v.2) / 2 + 1 / 2 ^ k)) +
      L * ((|v.1| - v.1) / 2 + 1 / 2 ^ k + v.1 + ((|v.2| - v.2) / 2 + 1 / 2 ^ k + v.2)) := by
    ring
  rw [e]
  linarith

lemma P_sub_le (v w : ℝ × ℝ) : P N v - P N w ≤ L * (|v.1 - w.1| + |v.2 - w.2|) := by
  have h1 := h.P_add w (v - w)
  rw [add_sub_cancel] at h1
  have h2 := h.P_le (v - w)
  simp only [Prod.fst_sub, Prod.snd_sub] at h2
  linarith

lemma P_cont : Continuous (P N) := by
  have hL := h.L_nonneg
  refine Metric.continuous_iff.2 (fun b ε hε => ?_)
  refine ⟨ε / (2 * L + 1), by positivity, fun a hab => ?_⟩
  rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq] at hab
  rw [Real.dist_eq, abs_lt]
  have h1 := h.P_sub_le a b
  have h2 := h.P_sub_le b a
  rw [abs_sub_comm b.1, abs_sub_comm b.2] at h2
  have hs : L * (|a.1 - b.1| + |a.2 - b.2|) ≤ L * (2 * (ε / (2 * L + 1))) := by
    apply mul_le_mul_of_nonneg_left _ hL; linarith [hab.1, hab.2]
  have hlt : L * (2 * (ε / (2 * L + 1))) < ε := by
    have e : L * (2 * (ε / (2 * L + 1))) = 2 * L * ε / (2 * L + 1) := by ring
    rw [e, div_lt_iff₀ (by positivity)]
    nlinarith
  constructor <;> linarith

/-- (10) for `P`: the parallelogram inequality. -/
lemma par_le (v w : ℝ × ℝ) : P N (v + w) ^ 2 + P N (v - w) ^ 2 ≤ 2 * P N v ^ 2 + 2 * P N w ^ 2 := by
  set y : ℝ × ℝ := (1 + 2 * |v.1| + 2 * |w.1|, 1 + 2 * |v.2| + 2 * |w.2|) with hy
  have a1 := neg_abs_le v.1
  have a2 := neg_abs_le v.2
  have a3 := neg_abs_le w.1
  have a4 := neg_abs_le w.2
  have b1 := abs_nonneg v.1
  have b2 := abs_nonneg v.2
  have b3 := abs_nonneg w.1
  have b4 := abs_nonneg w.2
  have hy1 : 0 < y.1 := by simp only [hy]; linarith
  have hy2 : 0 < y.2 := by simp only [hy]; linarith
  have hyQ : InQ y := ⟨hy1.le, hy2.le⟩
  have h2v : InQ (y + (2 : ℝ) • v) := by
    constructor <;> simp only [hy, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] <;> linarith
  have h2w : InQ (y + (2 : ℝ) • w) := by
    constructor <;> simp only [hy, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] <;> linarith
  have hyw1 : 0 < (y + w).1 := by simp only [hy, Prod.fst_add]; linarith
  have hyw2 : 0 < (y + w).2 := by simp only [hy, Prod.snd_add]; linarith
  have hyv : InQ (y + v) := by
    constructor <;> simp only [hy, Prod.fst_add, Prod.snd_add] <;> linarith
  have hyvw : InQ (y + (v + w)) := by
    constructor <;> simp only [hy, Prod.fst_add, Prod.snd_add] <;> linarith
  have hq := h.quad y y (y + (2 : ℝ) • v) (y + (2 : ℝ) • w) hyQ hyQ h2v h2w
  have e1 : mid y y = y := mid_self y
  have e2 : mid (y + (2 : ℝ) • v) (y + (2 : ℝ) • w) = y + (v + w) := by
    ext <;> simp [mid] <;> ring
  have e3 : mid y (y + (2 : ℝ) • w) = y + w := by ext <;> simp [mid] <;> ring
  have e4 : mid (y + (2 : ℝ) • v) y = (y + w) + (v - w) := by ext <;> simp [mid] <;> ring
  rw [e1, e2, e3, e4] at hq
  have hyw' : InQ (y + w + (v - w)) := by
    have : y + w + (v - w) = y + v := by abel
    rw [this]; exact hyv
  rw [h.P_eq_int hy1 hy2 hyvw, h.P_eq_int hyw1 hyw2 hyw', h.P_eq_int hy1 hy2 h2v,
    h.P_eq_int hy1 hy2 h2w, h.P_two, h.P_two] at hq
  linarith

lemma P_halfsmul (v : ℝ × ℝ) : P N ((1 / 2 : ℝ) • v) = P N v / 2 := by
  have := h.P_half v 1
  norm_num at this ⊢
  exact this

/-- The parallelogram law for `P²`. -/
lemma par (v w : ℝ × ℝ) : P N (v + w) ^ 2 + P N (v - w) ^ 2 = 2 * P N v ^ 2 + 2 * P N w ^ 2 := by
  refine le_antisymm (h.par_le v w) ?_
  have := h.par_le ((1 / 2 : ℝ) • (v + w)) ((1 / 2 : ℝ) • (v - w))
  have e1 : (1 / 2 : ℝ) • (v + w) + (1 / 2 : ℝ) • (v - w) = v := by
    ext <;> simp <;> ring
  have e2 : (1 / 2 : ℝ) • (v + w) - (1 / 2 : ℝ) • (v - w) = w := by
    ext <;> simp <;> ring
  rw [e1, e2, h.P_halfsmul, h.P_halfsmul] at this
  nlinarith

/-- The polarisation `B v w = (P(v+w)² - P(v-w)²) / 4`. -/
def Bf (N : ℝ × ℝ → ℝ × ℝ → ℝ) (v w : ℝ × ℝ) : ℝ := (P N (v + w) ^ 2 - P N (v - w) ^ 2) / 4

lemma B_zero_left (z : ℝ × ℝ) : Bf N 0 z = 0 := by
  simp only [Bf, zero_add, zero_sub, h.P_neg]; ring

lemma B_two (x z : ℝ × ℝ) : Bf N x ((2 : ℝ) • z) = 2 * Bf N x z := by
  have p1 := h.par (x + z) z
  have p2 := h.par (x - z) z
  have p3 := h.par x z
  have e1 : x + z + z = x + (2 : ℝ) • z := by rw [two_smul, add_assoc]
  have e2 : x + z - z = x := by abel
  have e3 : x - z + z = x := by abel
  have e4 : x - z - z = x - (2 : ℝ) • z := by rw [two_smul, sub_sub]
  rw [e1, e2] at p1
  rw [e3, e4] at p2
  simp only [Bf]
  linarith

lemma B_add_left (x y z : ℝ × ℝ) : Bf N (x + y) z = Bf N x z + Bf N y z := by
  have p1 := h.par (x + z) (y + z)
  have p2 := h.par (x - z) (y - z)
  have e1 : x + z + (y + z) = (x + y) + (2 : ℝ) • z := by rw [two_smul]; abel
  have e2 : x + z - (y + z) = x - y := by abel
  have e3 : x - z + (y - z) = (x + y) - (2 : ℝ) • z := by rw [two_smul]; abel
  have e4 : x - z - (y - z) = x - y := by abel
  rw [e1, e2] at p1
  rw [e3, e4] at p2
  have hb := h.B_two (x + y) z
  simp only [Bf] at hb ⊢
  linarith

lemma B_comm (x z : ℝ × ℝ) : Bf N x z = Bf N z x := by
  simp only [Bf]
  rw [add_comm x z, ← h.P_neg (x - z), neg_sub]

lemma B_self (x : ℝ × ℝ) : Bf N x x = P N x ^ 2 := by
  simp only [Bf, sub_self, h.P_zero]
  rw [← two_smul ℝ x, h.P_two]
  ring

lemma B_cont (z : ℝ × ℝ) : Continuous (fun x => Bf N x z) := by
  have hc := h.P_cont
  simp only [Bf]
  fun_prop

/-- `x ↦ B x z` as an additive map. -/
def BL (z : ℝ × ℝ) : (ℝ × ℝ) →+ ℝ where
  toFun x := Bf N x z
  map_zero' := h.B_zero_left z
  map_add' x y := h.B_add_left x y z

lemma B_smul_left (t : ℝ) (x z : ℝ × ℝ) : Bf N (t • x) z = t * Bf N x z := by
  have := map_real_smul (h.BL z) (h.B_cont z) t x
  simpa [BL] using this

/-- The quadratic form. -/
lemma P_sq (w : ℝ × ℝ) :
    P N w ^ 2 = w.1 ^ 2 * P N (1, 0) ^ 2 + 2 * w.1 * w.2 * Bf N (1, 0) (0, 1) +
      w.2 ^ 2 * P N (0, 1) ^ 2 := by
  have ew : w = w.1 • ((1 : ℝ), (0 : ℝ)) + w.2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
  rw [← h.B_self w]
  conv_lhs => rw [ew]
  rw [h.B_add_left, h.B_smul_left, h.B_smul_left, h.B_comm (1, 0), h.B_comm (0, 1),
    h.B_add_left, h.B_add_left, h.B_smul_left, h.B_smul_left, h.B_smul_left, h.B_smul_left,
    h.B_self, h.B_self, h.B_comm (0, 1) (1, 0)]
  ring

/-- Translation invariance including boundary base points. -/
lemma P_eq {z v : ℝ × ℝ} (hz : InQ z) (hzv : InQ (z + v)) : N z (z + v) = P N v := by
  refine le_antisymm ?_ (h.cmp (cpt_pos1 v) (cpt_pos2 v) hz hzv (cpt_add v))
  have c0 : InQ (z + ((1 : ℝ), (1 : ℝ))) := by
    constructor <;> simp <;> linarith [hz.1, hz.2]
  refine le_of_le_add_div_pow (C := N z (z + ((1 : ℝ), (1 : ℝ))) + P N ((1 : ℝ), (1 : ℝ)))
    (fun k => ?_)
  set e : ℝ × ℝ := (1 / 2 ^ k : ℝ) • ((1 : ℝ), (1 : ℝ)) with he
  have hk : (0 : ℝ) < 1 / 2 ^ k := by positivity
  have hze1 : 0 < (z + e).1 := by
    simp only [he, Prod.fst_add, Prod.smul_fst, smul_eq_mul, mul_one]; linarith [hz.1]
  have hze2 : 0 < (z + e).2 := by
    simp only [he, Prod.snd_add, Prod.smul_snd, smul_eq_mul, mul_one]; linarith [hz.2]
  have ee : z + e + (v - e) = z + v := by abel
  have t := h.tri z (z + e) (z + v) hz ⟨hze1.le, hze2.le⟩ hzv
  have d1 := h.dcs hz c0 k
  rw [← he] at d1
  have d2 := h.P_eq_int hze1 hze2 (by rw [ee]; exact hzv)
  rw [ee] at d2
  have d3 := h.P_add v (-e)
  rw [← sub_eq_add_neg, h.P_neg] at d3
  have d4 : P N e = P N ((1 : ℝ), (1 : ℝ)) / 2 ^ k := by rw [he]; exact h.P_half _ k
  rw [d1, d2] at t
  have e2 : (N z (z + ((1 : ℝ), (1 : ℝ))) + P N ((1 : ℝ), (1 : ℝ))) / 2 ^ k =
      N z (z + ((1 : ℝ), (1 : ℝ))) / 2 ^ k + P N ((1 : ℝ), (1 : ℝ)) / 2 ^ k := by ring
  rw [e2]
  linarith

/-- **The quadrant lemma.** -/
theorem formula {z z' : ℝ × ℝ} (hz : InQ z) (hz' : InQ z') :
    N z z' ^ 2 = (z'.1 - z.1) ^ 2 * N 0 (1, 0) ^ 2
      + (z'.1 - z.1) * (z'.2 - z.2) * (N 0 (1, 0) ^ 2 + N 0 (0, 1) ^ 2 - N (0, 1) (1, 0) ^ 2)
      + (z'.2 - z.2) ^ 2 * N 0 (0, 1) ^ 2 := by
  have h0 : InQ (0 : ℝ × ℝ) := ⟨le_rfl, le_rfl⟩
  have he1 : InQ ((1 : ℝ), (0 : ℝ)) := ⟨by norm_num, le_rfl⟩
  have he2 : InQ ((0 : ℝ), (1 : ℝ)) := ⟨le_rfl, by norm_num⟩
  have a1 : N 0 (1, 0) = P N (1, 0) := by
    have := h.P_eq h0 (v := (1, 0)) (by simpa using he1)
    simpa using this
  have a2 : N 0 (0, 1) = P N (0, 1) := by
    have := h.P_eq h0 (v := (0, 1)) (by simpa using he2)
    simpa using this
  have a3 : N (0, 1) (1, 0) = P N ((1, 0) - (0, 1)) := by
    have := h.P_eq he2 (v := ((1 : ℝ), (0 : ℝ)) - (0, 1)) (by simpa using he1)
    simpa using this
  have ezz : z + (z' - z) = z' := by abel
  have hN : N z z' = P N (z' - z) := by
    have := h.P_eq hz (v := z' - z) (by rw [ezz]; exact hz')
    rwa [ezz] at this
  have hB : P N ((1, 0) - (0, 1)) ^ 2 =
      P N (1, 0) ^ 2 - 2 * Bf N (1, 0) (0, 1) + P N (0, 1) ^ 2 := by
    rw [h.P_sq]; simp; ring
  rw [hN, a1, a2, a3, hB, h.P_sq]
  simp only [Prod.fst_sub, Prod.snd_sub]
  ring

end QHyp

end OM.NNN30.Geom
