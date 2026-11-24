import Mathlib

/-!
# The complete eleven-slot moment and its quadratic majorants: analytic part -/

noncomputable section
open Set
namespace OM.NNN18

def ell (z : ℝ) : ℝ := Real.logb 2 (1 + 10 * (2 : ℝ) ^ (3 * z)) - Real.logb 2 11

def prob (z : ℝ) : ℝ := 10 * (2 : ℝ) ^ (3 * z) / (1 + 10 * (2 : ℝ) ^ (3 * z))

lemma prob_mem (z : ℝ) : 0 ≤ prob z ∧ prob z ≤ 1 := by
  have hd : 0 < 1 + 10 * (2 : ℝ) ^ (3 * z) := by positivity
  refine ⟨by unfold prob; positivity, (div_le_one hd).2 (by linarith)⟩

lemma hasDerivAt_ell (z : ℝ) : HasDerivAt ell (3 * prob z) z := by
  have he := (HasDerivAt.const_rpow (by norm_num : (0 : ℝ) < 2)
    ((hasDerivAt_id z).const_mul 3)).const_mul (10 : ℝ)
  have hl := (((hasDerivAt_const z (1 : ℝ)).add he).log (by dsimp; positivity)).div_const
    (Real.log 2)
  have hn : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  convert! hl.sub_const (Real.logb 2 11) using 1
  dsimp [prob]
  field_simp
  ring

lemma hasDerivAt_slope (z : ℝ) :
    HasDerivAt (fun w => 3 * prob w) (9 * Real.log 2 * prob z * (1 - prob z)) z := by
  have he := (HasDerivAt.const_rpow (by norm_num : (0 : ℝ) < 2)
    ((hasDerivAt_id z).const_mul 3)).const_mul (10 : ℝ)
  have hd : 1 + 10 * (2 : ℝ) ^ (3 * z) ≠ 0 := by positivity
  have hq := (he.div ((hasDerivAt_const z (1 : ℝ)).add he) hd).const_mul 3
  convert! hq using 1
  dsimp [prob]
  field_simp
  ring

lemma ell_mono : Monotone ell :=
  monotone_of_hasDerivAt_nonneg hasDerivAt_ell (fun z => by
    have := (prob_mem z).1; positivity)

lemma prob_mono : Monotone prob := by
  intro a b hab
  have ha : (2 : ℝ) ^ (3 * a) ≤ (2 : ℝ) ^ (3 * b) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h0 : 0 < (2 : ℝ) ^ (3 * a) := by positivity
  unfold prob
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- Global curvature: `ell'' ≤ 2·(39/50)`, from `p(1-p) ≤ 1/4` and `ln 2 < 0.6931471808`. -/
lemma ell_second_le (z : ℝ) : 9 * Real.log 2 * prob z * (1 - prob z) ≤ 2 * (39 / 50) := by
  obtain ⟨h0, h1⟩ := prob_mem z
  have hv : prob z * (1 - prob z) ≤ 1 / 4 := by nlinarith [sq_nonneg (prob z - 1 / 2)]
  have hv0 : 0 ≤ prob z * (1 - prob z) := mul_nonneg h0 (by linarith)
  have hl := Real.log_two_lt_d9
  have hl0 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  nlinarith [mul_le_mul hl.le hv hv0 (by norm_num : (0 : ℝ) ≤ 0.6931471808)]

/-- On `z ≥ -1/2`: `2^{3z} ≥ 7/20`, so `p ≥ 7/9` and `ell'' ≤ 2·(11/20)`. -/
lemma ell_second_le_packed {z : ℝ} (hz : -1 / 2 ≤ z) :
    9 * Real.log 2 * prob z * (1 - prob z) ≤ 2 * (11 / 20) := by
  have hs : (7 : ℝ) / 20 ≤ (2 : ℝ) ^ (3 * z) := by
    have h1 : (2 : ℝ) ^ (-(3 : ℝ) / 2) ≤ (2 : ℝ) ^ (3 * z) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h2 : (7 : ℝ) / 20 ≤ (2 : ℝ) ^ (-(3 : ℝ) / 2) := by
      have hsq : ((2 : ℝ) ^ (-(3 : ℝ) / 2)) ^ 2 = 1 / 8 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        norm_num [Real.rpow_neg, Real.rpow_natCast]
      have hp : 0 ≤ (2 : ℝ) ^ (-(3 : ℝ) / 2) := by positivity
      nlinarith
    linarith
  have hp : 7 / 9 ≤ prob z := by
    unfold prob
    rw [le_div_iff₀ (by positivity)]
    linarith
  have h1 := (prob_mem z).2
  have hv : prob z * (1 - prob z) ≤ 14 / 81 := by nlinarith
  have hv0 : 0 ≤ prob z * (1 - prob z) := mul_nonneg (by linarith) (by linarith)
  have hl := Real.log_two_lt_d9
  have hl0 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  nlinarith [mul_le_mul hl.le hv hv0 (by norm_num : (0 : ℝ) ≤ 0.6931471808)]

/-- Taylor upper bound from a curvature bound on `[a, ∞)`. -/
theorem quad_upper_on {f f' f'' : ℝ → ℝ} {C a : ℝ}
    (hd : ∀ x, HasDerivAt f (f' x) x) (hdd : ∀ x, HasDerivAt f' (f'' x) x)
    (hC : ∀ x, a ≤ x → f'' x ≤ 2 * C) {c x : ℝ} (hc : a ≤ c) (hx : a ≤ x) :
    f x ≤ f c + f' c * (x - c) + C * (x - c) ^ 2 := by
  let g := fun y => C * (y - c) ^ 2 - f y
  let g' := fun y => 2 * C * (y - c) - f' y
  have hg (y) : HasDerivAt g (g' y) y := by
    convert! ((((hasDerivAt_id y).sub_const c).pow 2).const_mul C).sub (hd y) using 1 <;>
      (try dsimp [g, g']) <;> ring
  have hgg (y) : HasDerivAt g' (2 * C - f'' y) y := by
    convert! (((hasDerivAt_id y).sub_const c).const_mul (2 * C)).sub (hdd y) using 1 <;>
      (try dsimp [g']) <;> ring
  have hconv : ConvexOn ℝ (Ici a) g := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ici a)
      (fun y _ => (hg y).continuousAt.continuousWithinAt)
      (fun y _ => (hg y).hasDerivWithinAt) (fun y _ => (hgg y).hasDerivWithinAt)
    intro y hy
    rw [interior_Ici] at hy
    linarith [hC y (le_of_lt hy)]
  have key : g c + g' c * (x - c) ≤ g x := by
    rcases lt_trichotomy c x with h | h | h
    · have hh := hconv.le_slope_of_hasDerivAt hc hx h (hg c)
      rw [slope_def_field] at hh
      have := (le_div_iff₀ (sub_pos.mpr h)).1 hh
      linarith
    · subst h; simp
    · have hh := hconv.slope_le_of_hasDerivAt hx hc h (hg c)
      rw [slope_def_field] at hh
      have := (div_le_iff₀ (sub_pos.mpr h)).1 hh
      nlinarith
  nlinarith

theorem ell_le_majorant {a z0 z A0 A1 K c plo phi : ℝ}
    (hK : ∀ w, a ≤ w → 9 * Real.log 2 * prob w * (1 - prob w) ≤ 2 * K)
    (ha0 : a ≤ z0) (ha : a ≤ z) (hz : |z - z0| ≤ 2)
    (hc : ell z0 ≤ c) (hplo : plo ≤ 3 * prob z0) (hphi : 3 * prob z0 ≤ phi)
    (hcush : 2 * max (A1 - plo) (phi - A1) ≤ A0 - c) :
    ell z ≤ A0 + A1 * (z - z0) + K * (z - z0) ^ 2 := by
  have ht := quad_upper_on (f := ell) (f' := fun w => 3 * prob w) hasDerivAt_ell
    hasDerivAt_slope hK ha0 ha
  have hm1 := le_max_left (A1 - plo) (phi - A1)
  have hm2 := le_max_right (A1 - plo) (phi - A1)
  have habs := abs_le.1 hz
  have hlin : (3 * prob z0 - A1) * (z - z0) ≤ 2 * max (A1 - plo) (phi - A1) := by
    rcases le_total 0 (z - z0) with h | h
    · nlinarith
    · nlinarith
  nlinarith

/-! ## Rational enclosures of `exp` and of powers of two -/

def expTaylor (a : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => expTaylor a n + a ^ n / (n.factorial : ℚ)

def expRem (a : ℚ) : ℚ := a ^ 14 * 15 / ((Nat.factorial 14 : ℚ) * 14)
def expLo (a : ℚ) : ℚ := expTaylor a 14 - expRem a
def expHi (a : ℚ) : ℚ := expTaylor a 14 + expRem a

lemma expTaylor_cast (a : ℚ) (n : ℕ) :
    ((expTaylor a n : ℚ) : ℝ) = ∑ m ∈ Finset.range n, (a : ℝ) ^ m / m.factorial := by
  induction n with
  | zero => simp [expTaylor]
  | succ n ih => rw [expTaylor, Finset.sum_range_succ]; push_cast; rw [ih]

lemma exp_mem (a : ℚ) (h0 : 0 ≤ a) (h1 : a ≤ 1) :
    ((expLo a : ℚ) : ℝ) ≤ Real.exp a ∧ Real.exp a ≤ ((expHi a : ℚ) : ℝ) := by
  have ha0 : (0 : ℝ) ≤ a := by exact_mod_cast h0
  have ha1 : (a : ℝ) ≤ 1 := by exact_mod_cast h1
  have hb := Real.exp_bound (x := (a : ℝ)) (by rw [abs_of_nonneg ha0]; exact ha1)
    (n := 14) (by norm_num)
  rw [abs_of_nonneg ha0, abs_le] at hb
  have hr : ((expRem a : ℚ) : ℝ) = (a : ℝ) ^ 14 * ((Nat.succ 14 : ℕ) / ((Nat.factorial 14 : ℕ) * (14 : ℕ))) := by
    simp only [expRem]; push_cast; ring
  simp only [expLo, expHi, Rat.cast_sub, Rat.cast_add, expTaylor_cast, hr]
  constructor <;> linarith [hb.1, hb.2]

lemma expTaylor_ge_one (a : ℚ) (h0 : 0 ≤ a) : ∀ n, 1 ≤ n → 1 ≤ expTaylor a n
  | 0, h => absurd h (by norm_num)
  | 1, _ => by simp [expTaylor]
  | n + 2, _ => by
    have ih := expTaylor_ge_one a h0 (n + 1) (by omega)
    have : 0 ≤ a ^ (n + 1) / ((n + 1).factorial : ℚ) := by positivity
    simp only [expTaylor] at ih ⊢
    linarith

lemma expLo_pos (a : ℚ) (h0 : 0 ≤ a) (h1 : a ≤ 1) : 0 < expLo a := by
  have ht := expTaylor_ge_one a h0 14 (by norm_num)
  have hr : expRem a ≤ 15 / ((Nat.factorial 14 : ℚ) * 14) := by
    unfold expRem
    have : a ^ 14 ≤ 1 := pow_le_one₀ h0 h1
    have hf : (0 : ℚ) < (Nat.factorial 14 : ℚ) * 14 := by positivity
    rw [div_le_div_iff_of_pos_right hf]
    nlinarith
  have hs : (15 : ℚ) / ((Nat.factorial 14 : ℚ) * 14) < 1 := by
    rw [div_lt_one (by positivity)]; norm_num [Nat.factorial]
  unfold expLo; linarith

def Llo : ℚ := 6931471803 / 10000000000
def Lhi : ℚ := 6931471808 / 10000000000

/-- `2^{-(m+f)} ∈ [2^{-m}/expHi(f·Lhi), 2^{-m}/expLo(f·Llo)]` for `0 ≤ f ≤ 1`. -/
theorem two_rpow_mem (m : ℕ) (f : ℚ) (h0 : 0 ≤ f) (h1 : f ≤ 1) :
    ((1 / 2 ^ m / expHi (f * Lhi) : ℚ) : ℝ) ≤ (2 : ℝ) ^ (-(m : ℝ) - f) ∧
      (2 : ℝ) ^ (-(m : ℝ) - f) ≤ ((1 / 2 ^ m / expLo (f * Llo) : ℚ) : ℝ) := by
  have hL1 : Llo ≤ Lhi := by norm_num [Llo, Lhi]
  have hlo0 : 0 ≤ f * Llo := mul_nonneg h0 (by norm_num [Llo])
  have hhi1 : f * Lhi ≤ 1 := by
    have : Lhi ≤ 1 := by norm_num [Lhi]
    nlinarith
  have hlo1 : f * Llo ≤ 1 := le_trans (mul_le_mul_of_nonneg_left hL1 h0) hhi1
  have hhi0 : 0 ≤ f * Lhi := le_trans hlo0 (mul_le_mul_of_nonneg_left hL1 h0)
  obtain ⟨eA, eB⟩ := exp_mem (f * Llo) hlo0 hlo1
  obtain ⟨eC, eD⟩ := exp_mem (f * Lhi) hhi0 hhi1
  have hpos := expLo_pos (f * Llo) hlo0 hlo1
  have hposR : (0 : ℝ) < ((expLo (f * Llo) : ℚ) : ℝ) := by exact_mod_cast hpos
  have hf0 : (0 : ℝ) ≤ f := by exact_mod_cast h0
  have hlog_lo : ((Llo : ℚ) : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9; simp only [Llo]; push_cast; linarith
  have hlog_hi : Real.log 2 ≤ ((Lhi : ℚ) : ℝ) := by
    have := Real.log_two_lt_d9; simp only [Lhi]; push_cast; linarith
  -- exp(f log 2) between exp(f Llo) and exp(f Lhi)
  have hE1 : Real.exp ((f * Llo : ℚ) : ℝ) ≤ Real.exp ((f : ℝ) * Real.log 2) := by
    apply Real.exp_le_exp.2; push_cast; exact mul_le_mul_of_nonneg_left hlog_lo hf0
  have hE2 : Real.exp ((f : ℝ) * Real.log 2) ≤ Real.exp ((f * Lhi : ℚ) : ℝ) := by
    apply Real.exp_le_exp.2; push_cast; exact mul_le_mul_of_nonneg_left hlog_hi hf0
  have hsplit : (2 : ℝ) ^ (-(m : ℝ) - f) = (1 / 2 ^ m) / Real.exp ((f : ℝ) * Real.log 2) := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_neg (by norm_num), Real.rpow_natCast,
      Real.rpow_def_of_pos (by norm_num), mul_comm (Real.log 2)]
    field_simp
  rw [hsplit]
  have hX : 0 < Real.exp ((f : ℝ) * Real.log 2) := Real.exp_pos _
  have h2m : (0 : ℝ) < 1 / 2 ^ m := by positivity
  push_cast
  constructor
  · apply div_le_div_of_nonneg_left h2m.le hX (eD.trans' hE2)
  · apply div_le_div_of_nonneg_left h2m.le (by exact_mod_cast hpos) (eA.trans hE1)

/-- Lower bound for `log₂` via a rational lower bound for `2^c`. -/
lemma logb_le_of_le_two_rpow {Y c : ℝ} (hY : 0 < Y) (h : Y ≤ (2 : ℝ) ^ c) :
    Real.logb 2 Y ≤ c :=
  (Real.logb_le_iff_le_rpow (by norm_num) hY).2 h

lemma ell_eq (z : ℝ) : ell z = Real.logb 2 ((1 + 10 * (2 : ℝ) ^ (3 * z)) / 11) := by
  rw [ell, Real.logb_div (by positivity) (by norm_num)]

lemma three_prob_eq (z : ℝ) : 3 * prob z = 30 * (2 : ℝ) ^ (3 * z) / (1 + 10 * (2 : ℝ) ^ (3 * z)) := by
  unfold prob; ring

/-- `s ↦ 30 s/(1+10 s)` is monotone on `s ≥ 0`. -/
lemma slope_of_s_mono {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    30 * s / (1 + 10 * s) ≤ 30 * t / (1 + 10 * t) := by
  rw [div_le_div_iff₀ (by positivity) (by linarith)]
  nlinarith

/-- A rational certificate at the centre gives the majorant on `|z - z0| ≤ 2`, `z ≥ a`.
`3 z0 = -(m+f)`; the moment value is bounded by `c = -(mc+fc)`; all checks are in `ℚ`. -/
theorem bracket_of_cert (a : ℝ) {z0 : ℝ} {A0 A1 K : ℚ} (m mc : ℕ) (f fc : ℚ)
    (hK : ∀ w, a ≤ w → 9 * Real.log 2 * prob w * (1 - prob w) ≤ 2 * K)
    (hz0 : 3 * z0 = -(m : ℝ) - f) (hf0 : 0 ≤ f) (hf1 : f ≤ 1) (hfc0 : 0 ≤ fc) (hfc1 : fc ≤ 1)
    (hlog : (1 + 10 * (1 / 2 ^ m / expLo (f * Llo))) / 11 ≤ 1 / 2 ^ mc / expHi (fc * Lhi))
    (hcush : 2 * max (A1 - 30 * (1 / 2 ^ m / expHi (f * Lhi)) /
                        (1 + 10 * (1 / 2 ^ m / expHi (f * Lhi))))
                     (30 * (1 / 2 ^ m / expLo (f * Llo)) /
                        (1 + 10 * (1 / 2 ^ m / expLo (f * Llo))) - A1)
             ≤ A0 - (-(mc : ℚ) - fc))
    {z : ℝ} (ha0 : a ≤ z0) (ha : a ≤ z) (hz : |z - z0| ≤ 2) :
    ell z ≤ A0 + A1 * (z - z0) + K * (z - z0) ^ 2 := by
  obtain ⟨hslo, hshi⟩ := two_rpow_mem m f hf0 hf1
  obtain ⟨hclo, -⟩ := two_rpow_mem mc fc hfc0 hfc1
  rw [← hz0] at hslo hshi
  have hs0 : 0 ≤ (2 : ℝ) ^ (3 * z0) := by positivity
  set slo : ℚ := 1 / 2 ^ m / expHi (f * Lhi)
  set shi : ℚ := 1 / 2 ^ m / expLo (f * Llo)
  have hslo0 : (0 : ℝ) ≤ (slo : ℝ) := by
    have hpos : 0 < expHi (f * Lhi) := by
      have hL : 0 ≤ f * Lhi := mul_nonneg hf0 (by norm_num [Lhi])
      have hL1 : f * Lhi ≤ 1 := by
        have : Lhi ≤ 1 := by norm_num [Lhi]
        nlinarith
      have := expLo_pos (f * Lhi) hL hL1
      have hr : 0 ≤ expRem (f * Lhi) := by unfold expRem; positivity
      unfold expHi; unfold expLo at this; linarith
    have : (0 : ℚ) ≤ slo := by positivity
    exact_mod_cast this
  have hc : ell z0 ≤ ((-(mc : ℚ) - fc : ℚ) : ℝ) := by
    rw [ell_eq]
    apply logb_le_of_le_two_rpow (by positivity)
    have h1 : (1 + 10 * (2 : ℝ) ^ (3 * z0)) / 11 ≤ (1 + 10 * (shi : ℝ)) / 11 := by linarith
    have h2 : (1 + 10 * (shi : ℝ)) / 11 ≤ ((1 / 2 ^ mc / expHi (fc * Lhi) : ℚ) : ℝ) := by
      exact_mod_cast hlog
    have h3 : ((1 / 2 ^ mc / expHi (fc * Lhi) : ℚ) : ℝ) ≤ (2 : ℝ) ^ (-(mc : ℝ) - fc) := hclo
    have h4 : ((-(mc : ℚ) - fc : ℚ) : ℝ) = -(mc : ℝ) - fc := by push_cast; ring
    rw [h4]
    linarith
  have hplo : ((30 * slo / (1 + 10 * slo) : ℚ) : ℝ) ≤ 3 * prob z0 := by
    rw [three_prob_eq]; push_cast
    exact slope_of_s_mono hslo0 hslo
  have hphi : 3 * prob z0 ≤ ((30 * shi / (1 + 10 * shi) : ℚ) : ℝ) := by
    rw [three_prob_eq]; push_cast
    exact slope_of_s_mono hs0 hshi
  have hcushR : 2 * max ((A1 : ℝ) - ((30 * slo / (1 + 10 * slo) : ℚ) : ℝ))
      (((30 * shi / (1 + 10 * shi) : ℚ) : ℝ) - A1) ≤ (A0 : ℝ) - ((-(mc : ℚ) - fc : ℚ) : ℝ) := by
    have := hcush
    exact_mod_cast this
  exact ell_le_majorant hK ha0 ha hz hc hplo hphi hcushR

end OM.NNN18
