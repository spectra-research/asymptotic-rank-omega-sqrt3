import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.IntervalCases

/-! # Midpoint spaces

A `MidSpace X` is a pseudometric `d` on `X` with a midpoint map `m` satisfying the axial bounds (6)
`d(m(a,b), m(c,b)) ≤ d(a,c)/2`, `d(m(a,b), m(a,e)) ≤ d(b,e)/2`, `d(m(a,a), a) = 0` and the
quadrilateral inequality (10).  This file proves, for any such space:

* `m a b` is a metric midpoint: `d a (m a b) = d (m a b) b = d a b / 2`, and (9) (`bus`);
* quantitative uniqueness of midpoints (`mid_close`): a point `z` with `d a z + d z b = d a b`
  lies within `|d a z - d z b| / 2` of `m a b` ((10) at `(a, z, z, b)`);
* uniqueness of points on geodesics (`onSeg_unique`), by bisection;
* dyadic geodesic points `geo a b n k` (fraction `k / 2^n`, by bisection) with exact distances and
  Busemann convexity (11) at dyadic fractions.
-/

noncomputable section

namespace OM.NNN30.Geom

/-- A pseudometric space with a midpoint map satisfying (6), `m a a ≈ a` and (10). -/
structure MidSpace (X : Type*) where
  d : X → X → ℝ
  m : X → X → X
  d_self : ∀ x, d x x = 0
  d_comm : ∀ x y, d x y = d y x
  d_tri : ∀ x y z, d x z ≤ d x y + d y z
  ax1 : ∀ a b c, d (m a b) (m c b) ≤ d a c / 2
  ax2 : ∀ a b e, d (m a b) (m a e) ≤ d b e / 2
  ax3 : ∀ a, d (m a a) a = 0
  quad : ∀ a b c e, d (m a b) (m c e) ^ 2 + d (m a e) (m c b) ^ 2 ≤ (d a c ^ 2 + d b e ^ 2) / 2

namespace MidSpace

variable {X : Type*} (S : MidSpace X)

lemma d_nonneg (x y : X) : 0 ≤ S.d x y := by
  have h := S.d_tri x y x
  rw [S.d_self, S.d_comm y x] at h
  linarith

lemma le_left_mid (a b : X) : S.d a (S.m a b) ≤ S.d a b / 2 := by
  have h1 := S.d_tri a (S.m a a) (S.m a b)
  have h2 := S.ax2 a a b
  have h3 := S.ax3 a
  rw [S.d_comm a (S.m a a), h3] at h1
  linarith

lemma le_mid_right (a b : X) : S.d (S.m a b) b ≤ S.d a b / 2 := by
  have h1 := S.d_tri (S.m a b) (S.m b b) b
  have h2 := S.ax1 a b b
  rw [S.ax3 b] at h1
  linarith

lemma d_left_mid (a b : X) : S.d a (S.m a b) = S.d a b / 2 := by
  have := S.d_tri a (S.m a b) b
  linarith [S.le_left_mid a b, S.le_mid_right a b]

lemma d_mid_right (a b : X) : S.d (S.m a b) b = S.d a b / 2 := by
  have := S.d_tri a (S.m a b) b
  linarith [S.le_left_mid a b, S.le_mid_right a b]

/-- (9): `d(m(a,b), m(c,e)) ≤ (d(a,c) + d(b,e)) / 2`. -/
lemma bus (a b c e : X) : S.d (S.m a b) (S.m c e) ≤ (S.d a c + S.d b e) / 2 := by
  have h := S.d_tri (S.m a b) (S.m c b) (S.m c e)
  linarith [S.ax1 a b c, S.ax2 c b e]

lemma d_congr_left {x x' : X} (h : S.d x x' = 0) (y : X) : S.d x y = S.d x' y := by
  have h1 := S.d_tri x x' y
  have h2 := S.d_tri x' x y
  rw [S.d_comm x' x, h] at h2
  rw [h] at h1
  linarith

lemma d_congr_right (x : X) {y y' : X} (h : S.d y y' = 0) : S.d x y = S.d x y' := by
  rw [S.d_comm x y, S.d_comm x y']
  exact S.d_congr_left h x

lemma d_congr {x x' y y' : X} (hx : S.d x x' = 0) (hy : S.d y y' = 0) :
    S.d x y = S.d x' y' := by
  rw [S.d_congr_left hx y, S.d_congr_right x' hy]

lemma d_zero_trans {x y z : X} (h1 : S.d x y = 0) (h2 : S.d y z = 0) : S.d x z = 0 := by
  have := S.d_tri x y z
  linarith [S.d_nonneg x z]

lemma d_zero_symm {x y : X} (h : S.d x y = 0) : S.d y x = 0 := by
  rw [S.d_comm]; exact h

lemma sq_le_sq_imp {x y : ℝ} (hx : 0 ≤ x) (h : x ^ 2 ≤ y ^ 2) : x ≤ |y| := by
  have := sq_le_sq.1 h
  rwa [abs_of_nonneg hx] at this

/-- Quantitative uniqueness of midpoints ((10) at `(a, z, z, b)`). -/
lemma mid_close {a b z : X} {s t : ℝ} (hs : S.d a z = s) (ht : S.d z b = t)
    (hD : S.d a b = s + t) : S.d (S.m a b) z ≤ |s - t| / 2 := by
  have hq := S.quad a z z b
  have hl : (s + t) / 2 ≤ S.d (S.m a z) (S.m z b) := by
    have h1 := S.d_tri a (S.m a z) b
    have h2 := S.d_tri (S.m a z) (S.m z b) b
    have h3 := S.d_left_mid a z
    have h4 := S.d_mid_right z b
    linarith
  have hz : S.d (S.m a b) z ≤ S.d (S.m a b) (S.m z z) := by
    have := S.d_tri (S.m a b) (S.m z z) z
    rw [S.ax3 z] at this
    linarith
  have hs0 : 0 ≤ s := hs ▸ S.d_nonneg a z
  have ht0 : 0 ≤ t := ht ▸ S.d_nonneg z b
  have h0 : 0 ≤ (s + t) / 2 := by linarith
  have hsq : ((s + t) / 2) ^ 2 ≤ S.d (S.m a z) (S.m z b) ^ 2 := pow_le_pow_left₀ h0 hl 2
  rw [hs, ht] at hq
  have h5 : S.d (S.m a b) (S.m z z) ^ 2 ≤ ((s - t) / 2) ^ 2 := by nlinarith
  have h6 := sq_le_sq_imp (S.d_nonneg _ _) h5
  rw [abs_div, abs_two] at h6
  linarith

/-- `z` is on a geodesic from `a` to `b` at fraction `t`. -/
def OnSeg (a b z : X) (t : ℝ) : Prop :=
  S.d a z = t * S.d a b ∧ S.d z b = (1 - t) * S.d a b

lemma onSeg_of_le {a b z : X} {t : ℝ} (h1 : S.d a z ≤ t * S.d a b)
    (h2 : S.d z b ≤ (1 - t) * S.d a b) : S.OnSeg a b z t := by
  have h := S.d_tri a z b
  constructor <;> nlinarith

lemma onSeg_unique_aux (n : ℕ) : ∀ (a b z z' : X) (s : ℝ), 0 ≤ s → s ≤ S.d a b →
    S.d a z = s → S.d z b = S.d a b - s → S.d a z' = s → S.d z' b = S.d a b - s →
    S.d z z' ≤ 2 * S.d a b / 2 ^ n := by
  induction n with
  | zero =>
    intro a b z z' s _ hs1 h1 _ h3 _
    have := S.d_tri z a z'
    rw [S.d_comm z a] at this
    simp only [pow_zero, div_one]
    linarith
  | succ n ih =>
    intro a b z z' s hs0 hs1 h1 h2 h3 h4
    have hc1 := S.d_left_mid a b
    have hc2 := S.d_mid_right a b
    have hz := S.mid_close h1 h2 (by ring)
    have hz' := S.mid_close h3 h4 (by ring)
    have hp : (2 : ℝ) * (S.d a b / 2) / 2 ^ n = 2 * S.d a b / 2 ^ (n + 1) := by ring
    by_cases hs : s ≤ S.d a b / 2
    · have habs : |s - (S.d a b - s)| = S.d a b - 2 * s := by
        rw [abs_of_nonpos (by linarith)]; ring
      rw [habs] at hz hz'
      have e1 : S.d z (S.m a b) = S.d a (S.m a b) - s := by
        have := S.d_tri a z (S.m a b)
        have hzc := S.d_comm z (S.m a b)
        linarith
      have e2 : S.d z' (S.m a b) = S.d a (S.m a b) - s := by
        have := S.d_tri a z' (S.m a b)
        have hzc := S.d_comm z' (S.m a b)
        linarith
      have := ih a (S.m a b) z z' s hs0 (by rw [hc1]; exact hs) h1 e1 h3 e2
      rw [hc1, hp] at this
      exact this
    · replace hs := not_le.1 hs
      have habs : |s - (S.d a b - s)| = 2 * s - S.d a b := by
        rw [abs_of_nonneg (by linarith)]; ring
      rw [habs] at hz hz'
      have e1 : S.d (S.m a b) z = s - S.d a b / 2 := by
        have := S.d_tri (S.m a b) z b
        linarith
      have e2 : S.d (S.m a b) z' = s - S.d a b / 2 := by
        have := S.d_tri (S.m a b) z' b
        linarith
      have := ih (S.m a b) b z z' (s - S.d a b / 2) (by linarith) (by rw [hc2]; linarith)
        e1 (by rw [hc2]; linarith) e2 (by rw [hc2]; linarith)
      rw [hc2, hp] at this
      exact this

/-- Uniqueness of points on geodesics. -/
lemma onSeg_unique {a b z z' : X} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hz : S.OnSeg a b z t) (hz' : S.OnSeg a b z' t) : S.d z z' = 0 := by
  have hD := S.d_nonneg a b
  have key : ∀ n : ℕ, S.d z z' ≤ 2 * S.d a b / 2 ^ n := fun n =>
    S.onSeg_unique_aux n a b z z' (t * S.d a b) (by positivity)
      (by nlinarith) hz.1 (by rw [hz.2]; ring) hz'.1 (by rw [hz'.2]; ring)
  have h0 := S.d_nonneg z z'
  have hlim : Filter.Tendsto (fun n : ℕ => 2 * S.d a b / 2 ^ n) Filter.atTop (nhds 0) := by
    have h1 := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (2 * S.d a b)
    rw [mul_zero] at h1
    refine h1.congr (fun n => ?_)
    rw [one_div_pow]; ring
  have := ge_of_tendsto' hlim key
  linarith

lemma onSeg_mid (a b : X) : S.OnSeg a b (S.m a b) (1 / 2) := by
  constructor
  · rw [S.d_left_mid]; ring
  · rw [S.d_mid_right]; ring

/-! ## Dyadic geodesic points -/

/-- `geo a b n k` is the point at fraction `k / 2^n` from `a` to `b` (bisection). -/
def geo : X → X → ℕ → ℕ → X
  | a, b, 0, k => if k = 0 then a else b
  | a, b, n + 1, k => if k ≤ 2 ^ n then geo a (S.m a b) n k else geo (S.m a b) b n (k - 2 ^ n)

lemma geo_full (n : ℕ) : ∀ a b : X, S.geo a b n (2 ^ n) = b := by
  induction n with
  | zero => intro a b; simp [geo]
  | succ n ih =>
    intro a b
    have h : ¬ 2 ^ (n + 1) ≤ 2 ^ n := by
      rw [pow_succ]; have := Nat.one_le_two_pow (n := n); omega
    simp only [geo, h, ↓reduceIte]
    have : 2 ^ (n + 1) - 2 ^ n = 2 ^ n := by rw [pow_succ]; omega
    rw [this]
    exact ih _ _

/-- `geo a b (r + j) (2^j)` is `r` times halving towards `a`. -/
lemma geo_pow (r : ℕ) : ∀ (j : ℕ) (a b : X), S.geo a b (r + j) (2 ^ j) = (S.m a)^[r] b := by
  induction r with
  | zero => intro j a b; simp [S.geo_full]
  | succ r ih =>
    intro j a b
    have h : r + 1 + j = (r + j) + 1 := by omega
    rw [h]
    have hle : 2 ^ j ≤ 2 ^ (r + j) := Nat.pow_le_pow_right (by norm_num) (by omega)
    simp only [geo, hle, ↓reduceIte]
    rw [ih j a (S.m a b), Function.iterate_succ_apply]

lemma geo_dist (n : ℕ) : ∀ (a b : X) (k : ℕ), k ≤ 2 ^ n →
    S.d a (S.geo a b n k) = (k : ℝ) / 2 ^ n * S.d a b ∧
    S.d (S.geo a b n k) b = (1 - (k : ℝ) / 2 ^ n) * S.d a b := by
  induction n with
  | zero =>
    intro a b k hk
    have hk1 : k ≤ 1 := by simpa using hk
    interval_cases k
    · simp [geo, S.d_self]
    · simp [geo, S.d_self]
  | succ n ih =>
    intro a b k hk
    have hp : (k : ℝ) / 2 ^ (n + 1) = (k : ℝ) / 2 ^ n / 2 := by ring
    by_cases hkn : k ≤ 2 ^ n
    · simp only [geo, hkn, ↓reduceIte]
      obtain ⟨h1, h2⟩ := ih a (S.m a b) k hkn
      rw [S.d_left_mid] at h1 h2
      have h3 := S.d_mid_right a b
      have t1 := S.d_tri (S.geo a (S.m a b) n k) (S.m a b) b
      have t2 := S.d_tri a (S.geo a (S.m a b) n k) b
      rw [hp]
      constructor
      · rw [h1]; ring
      · linarith
    · replace hkn := not_le.1 hkn
      simp only [geo, not_le.2 hkn, ↓reduceIte]
      have hk' : k - 2 ^ n ≤ 2 ^ n := by rw [pow_succ] at hk; omega
      obtain ⟨h1, h2⟩ := ih (S.m a b) b (k - 2 ^ n) hk'
      rw [S.d_mid_right] at h1 h2
      have hc : ((k - 2 ^ n : ℕ) : ℝ) = (k : ℝ) - 2 ^ n := by
        rw [Nat.cast_sub hkn.le]; push_cast; ring
      rw [hc] at h1 h2
      have h3 := S.d_left_mid a b
      have t1 := S.d_tri a (S.m a b) (S.geo (S.m a b) b n (k - 2 ^ n))
      have t2 := S.d_tri a (S.geo (S.m a b) b n (k - 2 ^ n)) b
      have e : ((k : ℝ) - 2 ^ n) / 2 ^ n = (k : ℝ) / 2 ^ n - 1 := by field_simp
      rw [e] at h1 h2
      rw [hp]
      constructor
      · nlinarith [S.d_nonneg a b]
      · rw [h2]; ring

lemma geo_left (n : ℕ) (a b : X) {k : ℕ} (hk : k ≤ 2 ^ n) :
    S.d a (S.geo a b n k) = (k : ℝ) / 2 ^ n * S.d a b := (S.geo_dist n a b k hk).1

lemma geo_right (n : ℕ) (a b : X) {k : ℕ} (hk : k ≤ 2 ^ n) :
    S.d (S.geo a b n k) b = (1 - (k : ℝ) / 2 ^ n) * S.d a b := (S.geo_dist n a b k hk).2

/-- Distances between dyadic points of the same geodesic. -/
lemma geo_same_le (n : ℕ) : ∀ (a b : X) (k k' : ℕ), k ≤ k' → k' ≤ 2 ^ n →
    S.d (S.geo a b n k) (S.geo a b n k') ≤ ((k' : ℝ) - k) / 2 ^ n * S.d a b := by
  induction n with
  | zero =>
    intro a b k k' hkk hk'
    have hk1 : k' ≤ 1 := by simpa using hk'
    interval_cases k' <;> interval_cases k <;> simp [geo, S.d_self]
  | succ n ih =>
    intro a b k k' hkk hk'
    have hD := S.d_nonneg a b
    by_cases h1 : k' ≤ 2 ^ n
    · have h0 : k ≤ 2 ^ n := le_trans hkk h1
      simp only [geo, h1, h0, ↓reduceIte]
      have := ih a (S.m a b) k k' hkk h1
      rw [S.d_left_mid] at this
      calc _ ≤ _ := this
        _ = _ := by ring
    · replace h1 := not_le.1 h1
      by_cases h0 : k ≤ 2 ^ n
      · simp only [geo, h0, not_le.2 h1, ↓reduceIte]
        have hk'' : k' - 2 ^ n ≤ 2 ^ n := by rw [pow_succ] at hk'; omega
        have e1 := S.geo_right n a (S.m a b) h0
        have e2 := S.geo_left n (S.m a b) b hk''
        rw [S.d_left_mid] at e1
        rw [S.d_mid_right] at e2
        have hc : ((k' - 2 ^ n : ℕ) : ℝ) = (k' : ℝ) - 2 ^ n := by
          rw [Nat.cast_sub h1.le]; push_cast; ring
        rw [hc] at e2
        have t := S.d_tri (S.geo a (S.m a b) n k) (S.m a b) (S.geo (S.m a b) b n (k' - 2 ^ n))
        have e3 : ((k' : ℝ) - k) / 2 ^ (n + 1) * S.d a b =
            (1 - (k : ℝ) / 2 ^ n) * (S.d a b / 2) + ((k' : ℝ) - 2 ^ n) / 2 ^ n * (S.d a b / 2) := by
          field_simp; ring
        rw [e3]; linarith
      · replace h0 := not_le.1 h0
        simp only [geo, not_le.2 h1, not_le.2 h0, ↓reduceIte]
        have hk'' : k' - 2 ^ n ≤ 2 ^ n := by rw [pow_succ] at hk'; omega
        have := ih (S.m a b) b (k - 2 ^ n) (k' - 2 ^ n) (by omega) hk''
        rw [S.d_mid_right] at this
        have hc : ((k' - 2 ^ n : ℕ) : ℝ) - ((k - 2 ^ n : ℕ) : ℝ) = (k' : ℝ) - k := by
          rw [Nat.cast_sub h1.le, Nat.cast_sub h0.le]; ring
        rw [hc] at this
        calc _ ≤ _ := this
          _ = _ := by ring

lemma geo_same (n : ℕ) (a b : X) {k k' : ℕ} (hk : k ≤ 2 ^ n) (hk' : k' ≤ 2 ^ n) :
    S.d (S.geo a b n k) (S.geo a b n k') = |(k' : ℝ) - k| / 2 ^ n * S.d a b := by
  have hD := S.d_nonneg a b
  rcases le_total k k' with h | h
  · have hle := S.geo_same_le n a b k k' h hk'
    have e1 := S.geo_left n a b hk
    have e2 := S.geo_left n a b hk'
    have t := S.d_tri a (S.geo a b n k) (S.geo a b n k')
    have hkk : (k : ℝ) ≤ k' := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]
    have e3 : ((k' : ℝ) - k) / 2 ^ n * S.d a b = (k' : ℝ) / 2 ^ n * S.d a b - (k : ℝ) / 2 ^ n * S.d a b := by
      ring
    rw [e3] at hle ⊢
    linarith
  · have hle := S.geo_same_le n a b k' k h hk
    have e1 := S.geo_left n a b hk
    have e2 := S.geo_left n a b hk'
    have t := S.d_tri a (S.geo a b n k') (S.geo a b n k)
    have hkk : (k' : ℝ) ≤ k := by exact_mod_cast h
    rw [abs_of_nonpos (by linarith), S.d_comm]
    have e3 : ((k : ℝ) - k') / 2 ^ n * S.d a b = (k : ℝ) / 2 ^ n * S.d a b - (k' : ℝ) / 2 ^ n * S.d a b := by
      ring
    rw [e3] at hle
    have e4 : -((k' : ℝ) - k) / 2 ^ n * S.d a b = (k : ℝ) / 2 ^ n * S.d a b - (k' : ℝ) / 2 ^ n * S.d a b := by
      ring
    rw [e4]
    linarith

/-- Busemann convexity (11) at dyadic fractions. -/
lemma geo_bus (n : ℕ) : ∀ (a b c e : X) (k : ℕ), k ≤ 2 ^ n →
    S.d (S.geo a b n k) (S.geo c e n k) ≤
      (1 - (k : ℝ) / 2 ^ n) * S.d a c + (k : ℝ) / 2 ^ n * S.d b e := by
  induction n with
  | zero =>
    intro a b c e k hk
    have hk1 : k ≤ 1 := by simpa using hk
    interval_cases k <;> simp [geo]
  | succ n ih =>
    intro a b c e k hk
    have hp : (k : ℝ) / 2 ^ (n + 1) = (k : ℝ) / 2 ^ n / 2 := by ring
    by_cases hkn : k ≤ 2 ^ n
    · simp only [geo, hkn, ↓reduceIte]
      have h1 := ih a (S.m a b) c (S.m c e) k hkn
      have h2 := S.bus a b c e
      have hk0 : (0 : ℝ) ≤ (k : ℝ) / 2 ^ n := by positivity
      have hk1 : (k : ℝ) / 2 ^ n ≤ 1 := by
        rw [div_le_one (by positivity)]; exact_mod_cast hkn
      rw [hp]
      nlinarith [mul_le_mul_of_nonneg_left h2 hk0]
    · replace hkn := not_le.1 hkn
      simp only [geo, not_le.2 hkn, ↓reduceIte]
      have hk' : k - 2 ^ n ≤ 2 ^ n := by rw [pow_succ] at hk; omega
      have h1 := ih (S.m a b) b (S.m c e) e (k - 2 ^ n) hk'
      have h2 := S.bus a b c e
      have hc : ((k - 2 ^ n : ℕ) : ℝ) = (k : ℝ) - 2 ^ n := by
        rw [Nat.cast_sub hkn.le]; push_cast; ring
      rw [hc] at h1
      have e : ((k : ℝ) - 2 ^ n) / 2 ^ n = (k : ℝ) / 2 ^ n - 1 := by field_simp
      rw [e] at h1
      have hk0 : (0 : ℝ) ≤ 2 - (k : ℝ) / 2 ^ n := by
        have : (k : ℝ) ≤ 2 ^ (n + 1) := by exact_mod_cast hk
        rw [pow_succ] at this
        have h2n : (0 : ℝ) < 2 ^ n := by positivity
        rw [sub_nonneg, div_le_iff₀ h2n]; linarith
      rw [hp]
      nlinarith [mul_le_mul_of_nonneg_left h2 hk0]

end MidSpace

end OM.NNN30.Geom
