import Lib.OM.NNN20.TM.Basic

/-! # Semantics of the fixed-point Taylor models

`peval c x y = Σ_{i < 45} c_i x^{a_i} y^{b_i}` (integer coefficients, unscaled), and a Taylor
model `t` encloses `f : ℝ → ℝ → ℝ` (`t.Encl f`) when for every `(x, y)` in the box `[-1,1]^2`

  `t.lo ≤ ONE * f x y - peval t.c x y ≤ t.hi`.

This file proves the soundness of the linear operations, of the range bounds `rng`, of the
rational scalings `mulq`, `mulI` and of the constant constructors. -/

namespace OM.NNN20

open Finset

/-- exponents of the `i`-th monomial -/
def mx (i : ℕ) : ℕ × ℕ := MONO.getD i (0, 0)
/-- the `i`-th coefficient (zero beyond the list) -/
def cf (c : List ℤ) (i : ℕ) : ℤ := c.getD i 0

/-- the value of the monomial `i` -/
noncomputable def mono (i : ℕ) (x y : ℝ) : ℝ := x ^ (mx i).1 * y ^ (mx i).2

/-- the polynomial with (unscaled) coefficients `c` -/
noncomputable def peval (c : List ℤ) (x y : ℝ) : ℝ :=
  ∑ i ∈ range NM, (cf c i : ℝ) * mono i x y

lemma ONE_pos : (0 : ℝ) < ONE := by norm_num [ONE]
lemma ONE_eq : (ONE : ℝ) = 2 ^ 64 := by norm_num [ONE]

lemma mono_abs_le {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) (i : ℕ) : |mono i x y| ≤ 1 := by
  rw [mono, abs_mul, abs_pow, abs_pow]
  calc |x| ^ (mx i).1 * |y| ^ (mx i).2 ≤ 1 * 1 :=
        mul_le_mul (pow_le_one₀ (abs_nonneg _) hx) (pow_le_one₀ (abs_nonneg _) hy) (by positivity)
          zero_le_one
    _ = 1 := one_mul 1

/-! ## Coefficient lemmas -/

@[simp] lemma cf_nil (i : ℕ) : cf [] i = 0 := by simp [cf]
@[simp] lemma cf_cons_zero (a : ℤ) (as : List ℤ) : cf (a :: as) 0 = a := by simp [cf]
@[simp] lemma cf_cons_succ (a : ℤ) (as : List ℤ) (i : ℕ) : cf (a :: as) (i + 1) = cf as i := by
  simp [cf]

lemma cf_addL : ∀ (a b : List ℤ) (i : ℕ), cf (addL a b) i = cf a i + cf b i
  | x :: as, y :: bs, 0 => by simp [addL]
  | x :: as, y :: bs, i + 1 => by simp [addL, cf_addL as bs i]
  | [], bs, i => by simp [addL]
  | x :: as, [], i => by simp [addL]

lemma cf_map {f : ℤ → ℤ} (hf : f 0 = 0) : ∀ (c : List ℤ) (i : ℕ), cf (c.map f) i = f (cf c i)
  | [], i => by simp [hf]
  | a :: as, 0 => by simp
  | a :: as, i + 1 => by simp [cf_map hf as i]

lemma cf_negL (c : List ℤ) (i : ℕ) : cf (negL c) i = -cf c i := cf_map (by simp) c i
lemma cf_smulL (k : ℤ) (c : List ℤ) (i : ℕ) : cf (smulL k c) i = k * cf c i :=
  cf_map (by simp) c i

/-! ## Linear identities of `peval` -/

lemma peval_addL (a b : List ℤ) (x y : ℝ) : peval (addL a b) x y = peval a x y + peval b x y := by
  simp only [peval, cf_addL, Int.cast_add, add_mul, sum_add_distrib]

lemma peval_negL (c : List ℤ) (x y : ℝ) : peval (negL c) x y = -peval c x y := by
  simp only [peval, cf_negL, Int.cast_neg, neg_mul, sum_neg_distrib]

lemma peval_smulL (k : ℤ) (c : List ℤ) (x y : ℝ) : peval (smulL k c) x y = k * peval c x y := by
  simp only [peval, cf_smulL, Int.cast_mul, mul_sum, mul_assoc]

lemma l1_cons (a : ℤ) (as : List ℤ) : l1 (a :: as) = a.natAbs + l1 as := rfl

/-- `Σ_{i<n} |c_i| ≤ ℓ¹(c)` -/
lemma sum_abs_le_l1 : ∀ (c : List ℤ) (n : ℕ), ∑ i ∈ range n, |(cf c i : ℝ)| ≤ (l1 c : ℝ)
  | [], n => by simp [l1]
  | a :: as, 0 => by simp
  | a :: as, n + 1 => by
    rw [sum_range_succ']
    simp only [cf_cons_succ, cf_cons_zero, l1_cons, Nat.cast_add]
    have h := sum_abs_le_l1 as n
    have : |(a : ℝ)| = (a.natAbs : ℝ) := by rw [Nat.cast_natAbs, Int.cast_abs]
    linarith

lemma peval_abs_le (c : List ℤ) {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    |peval c x y| ≤ l1 c := by
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun i _ => ?_).trans (sum_abs_le_l1 c NM))
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (mono_abs_le hx hy i)

/-! ## Enclosures -/

/-- `t` encloses `f` on the box. -/
def TM.Encl (t : TM) (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, |x| ≤ 1 → |y| ≤ 1 →
    (t.lo : ℝ) ≤ (ONE : ℝ) * f x y - peval t.c x y ∧ (ONE : ℝ) * f x y - peval t.c x y ≤ t.hi

namespace TM

lemma Encl.congr {t : TM} {f g : ℝ → ℝ → ℝ} (h : t.Encl f) (hfg : ∀ x y, |x| ≤ 1 → |y| ≤ 1 → f x y = g x y) :
    t.Encl g := fun x y hx hy => by rw [← hfg x y hx hy]; exact h x y hx hy

theorem add_encl {t u : TM} {f g : ℝ → ℝ → ℝ} (ht : t.Encl f) (hu : u.Encl g) :
    (t.add u).Encl (fun x y => f x y + g x y) := by
  intro x y hx hy
  obtain ⟨h1, h2⟩ := ht x y hx hy
  obtain ⟨h3, h4⟩ := hu x y hx hy
  simp only [add, peval_addL, Int.cast_add]
  constructor <;> nlinarith

theorem neg_encl {t : TM} {f : ℝ → ℝ → ℝ} (ht : t.Encl f) : t.neg.Encl (fun x y => -f x y) := by
  intro x y hx hy
  obtain ⟨h1, h2⟩ := ht x y hx hy
  simp only [neg, peval_negL, Int.cast_neg]
  constructor <;> nlinarith

theorem sub_encl {t u : TM} {f g : ℝ → ℝ → ℝ} (ht : t.Encl f) (hu : u.Encl g) :
    (t.sub u).Encl (fun x y => f x y - g x y) := by
  have := add_encl ht (neg_encl hu)
  simpa [sub, sub_eq_add_neg] using this

theorem smul_encl (k : ℤ) {t : TM} {f : ℝ → ℝ → ℝ} (ht : t.Encl f) :
    (t.smul k).Encl (fun x y => k * f x y) := by
  intro x y hx hy
  obtain ⟨h1, h2⟩ := ht x y hx hy
  have e : (ONE : ℝ) * (k * f x y) - peval (smulL k t.c) x y =
      k * ((ONE : ℝ) * f x y - peval t.c x y) := by rw [peval_smulL]; ring
  unfold smul
  split_ifs with hk
  · have hk' : (0 : ℝ) ≤ k := by exact_mod_cast hk
    simp only [e, Int.cast_mul]
    exact ⟨mul_le_mul_of_nonneg_left h1 hk', mul_le_mul_of_nonneg_left h2 hk'⟩
  · have hk' : (k : ℝ) ≤ 0 := by exact_mod_cast (not_le.mp hk).le
    simp only [e, Int.cast_mul]
    exact ⟨mul_le_mul_of_nonpos_left h2 hk', mul_le_mul_of_nonpos_left h1 hk'⟩

lemma peval_single (m : ℤ) (x y : ℝ) : peval [m] x y = m := by
  rw [peval, NM, sum_range_succ']
  simp [cf, mono, mx, MONO]

theorem const_encl (m : ℤ) : (const m).Encl (fun _ _ => (m : ℝ) / ONE) := by
  intro x y _ _
  simp only [const, peval_single, Int.cast_zero]
  have : (ONE : ℝ) * ((m : ℝ) / ONE) = m := by
    rw [mul_div_assoc']; exact mul_div_cancel_left₀ _ ONE_pos.ne'
  rw [this]; simp

theorem widen_encl {t : TM} {f g : ℝ → ℝ → ℝ} (ht : t.Encl f) (e : ℤ)
    (hfg : ∀ x y, |x| ≤ 1 → |y| ≤ 1 → |(ONE : ℝ) * (g x y - f x y)| ≤ e) :
    (t.widen e).Encl g := by
  intro x y hx hy
  obtain ⟨h1, h2⟩ := ht x y hx hy
  have h := abs_le.mp (hfg x y hx hy)
  simp only [widen, Int.cast_sub, Int.cast_add]
  constructor <;> nlinarith

/-! ## Rational helpers -/

lemma qfloor_le (x : ℚ) : (qfloor x : ℚ) ≤ x := by
  unfold qfloor
  have hd : (0 : ℚ) < x.den := by exact_mod_cast x.den_pos
  have h1 : (x.num / (x.den : ℤ)) * (x.den : ℤ) ≤ x.num :=
    Int.ediv_mul_le x.num (by exact_mod_cast x.den_pos.ne')
  have h2 : ((x.num / (x.den : ℤ) : ℤ) : ℚ) * x.den ≤ x.num := by exact_mod_cast h1
  calc ((x.num / (x.den : ℤ) : ℤ) : ℚ) ≤ x.num / x.den := by rw [le_div_iff₀ hd]; exact h2
    _ = x := Rat.num_div_den x

lemma lt_qfloor_add_one (x : ℚ) : x < qfloor x + 1 := by
  unfold qfloor
  have hd : (0 : ℚ) < x.den := by exact_mod_cast x.den_pos
  have h1 : x.num < (x.num / (x.den : ℤ) + 1) * (x.den : ℤ) :=
    Int.lt_ediv_add_one_mul_self x.num (by exact_mod_cast x.den_pos)
  have h2 : (x.num : ℚ) < (((x.num / (x.den : ℤ) : ℤ) : ℚ) + 1) * x.den := by exact_mod_cast h1
  calc x = x.num / x.den := (Rat.num_div_den x).symm
    _ < ((x.num / (x.den : ℤ) : ℤ) : ℚ) + 1 := by rw [div_lt_iff₀ hd]; exact h2

lemma le_qceil (x : ℚ) : x ≤ qceil x := by
  have := qfloor_le (-x)
  simp only [qceil, Int.cast_neg]; linarith

lemma qceil_lt_add_one (x : ℚ) : (qceil x : ℚ) < x + 1 := by
  have := lt_qfloor_add_one (-x)
  simp only [qceil, Int.cast_neg]; linarith

lemma qfloor_le_real (x : ℚ) : ((qfloor x : ℤ) : ℝ) ≤ (x : ℝ) := by
  have := qfloor_le x; exact_mod_cast this
lemma lt_qfloor_add_one_real (x : ℚ) : (x : ℝ) < (qfloor x : ℝ) + 1 := by
  have := lt_qfloor_add_one x; exact_mod_cast this
lemma le_qceil_real (x : ℚ) : (x : ℝ) ≤ (qceil x : ℝ) := by
  have := le_qceil x; exact_mod_cast this

/-- `b * (a / b) ≤ a < b * (a / b) + b` for `b > 0` (floor division) -/
lemma ediv_bounds (a b : ℤ) (hb : 0 < b) :
    (b : ℝ) * ((a / b : ℤ) : ℝ) ≤ a ∧ (a : ℝ) < b * ((a / b : ℤ) : ℝ) + b := by
  have h1 := Int.ediv_mul_le a hb.ne'
  have h2 := Int.lt_ediv_add_one_mul_self a hb
  constructor
  · have : ((a / b) * b : ℤ) ≤ a := h1
    have : ((a / b : ℤ) : ℝ) * b ≤ a := by exact_mod_cast this
    linarith
  · have : (a : ℝ) < ((a / b + 1 : ℤ) : ℝ) * b := by exact_mod_cast h2
    push_cast at this; linarith

lemma cdiv_bounds (a b : ℤ) (hb : 0 < b) : (a : ℝ) ≤ b * (cdiv a b : ℝ) := by
  have := (ediv_bounds (-a) b hb).1
  simp only [cdiv, Int.cast_neg] at this ⊢
  linarith

/-! ## Constants and the affine coordinates -/

theorem constI_encl (a b : ℚ) {f : ℝ → ℝ → ℝ}
    (hf : ∀ x y, |x| ≤ 1 → |y| ≤ 1 → (a : ℝ) ≤ f x y ∧ f x y ≤ b) :
    (constI a b).Encl f := by
  intro x y hx hy
  obtain ⟨h1, h2⟩ := hf x y hx hy
  simp only [constI, peval_single, Int.cast_sub, Int.cast_zero]
  have hO := ONE_pos
  have e1 : ((qfloor (a * ONE) : ℤ) : ℝ) ≤ (a : ℝ) * ONE := by
    have := qfloor_le_real (a * ONE); push_cast at this; exact this
  have e2 : (b : ℝ) * ONE ≤ ((qceil (b * ONE) : ℤ) : ℝ) := by
    have := le_qceil_real (b * ONE); push_cast at this; exact this
  constructor <;> nlinarith

theorem ofq_encl (q : ℚ) : (ofq q).Encl (fun _ _ => (q : ℝ)) :=
  constI_encl q q (fun _ _ _ _ => ⟨le_rfl, le_rfl⟩)

end TM


/-! ## Range bounds -/

/-- finite facts about `MONO` and `EVEN` -/
lemma EVEN_spec : ∀ i < 44, EVEN.tail.getD i false = true →
    (mx (i + 1)).1 % 2 = 0 ∧ (mx (i + 1)).2 % 2 = 0 := by decide +kernel

lemma EVEN_tail_length : EVEN.tail.length = 44 := rfl

lemma mx_zero : mx 0 = (0, 0) := rfl

lemma mono_zero (x y : ℝ) : mono 0 x y = 1 := by simp [mono, mx_zero]

lemma rngAux_spec : ∀ (as : List ℤ) (evs : List Bool) (m : ℕ → ℝ),
    (∀ i < evs.length, |m i| ≤ 1) → (∀ i < evs.length, evs.getD i false = true → 0 ≤ m i) →
    ((TM.rngAux as evs).1 : ℝ) ≤ ∑ i ∈ range evs.length, (cf as i : ℝ) * m i ∧
    ∑ i ∈ range evs.length, (cf as i : ℝ) * m i ≤ (TM.rngAux as evs).2
  | [], evs, m, _, _ => by simp [TM.rngAux]
  | a :: as, [], m, _, _ => by simp [TM.rngAux]
  | a :: as, ev :: evs, m, h1, h2 => by
    have ih := rngAux_spec as evs (fun i => m (i + 1))
      (fun i hi => h1 (i + 1) (by simp; omega))
      (fun i hi he => h2 (i + 1) (by simp; omega) (by simpa using he))
    simp only [List.length_cons] at ih ⊢
    rw [sum_range_succ']
    simp only [cf_cons_succ, cf_cons_zero]
    have hm0 := h1 0 (by simp)
    have hab := abs_le.mp hm0
    obtain ⟨ih1, ih2⟩ := ih
    simp only [TM.rngAux]
    have habs : |(a : ℝ)| = (a.natAbs : ℝ) := by rw [Nat.cast_natAbs, Int.cast_abs]
    by_cases hev : ev = true
    · have hpos : 0 ≤ m 0 := h2 0 (by simp) (by simp [hev])
      simp only [hev, ite_true]
      simp only [Int.cast_add, Int.cast_max, Int.cast_min, Int.cast_zero]
      constructor
      · have : min 0 (a : ℝ) ≤ a * m 0 := by
          rcases le_total 0 (a : ℝ) with ha | ha
          · rw [min_eq_left ha]; positivity
          · rw [min_eq_right ha]; nlinarith
        linarith
      · have : (a : ℝ) * m 0 ≤ max 0 (a : ℝ) := by
          rcases le_total 0 (a : ℝ) with ha | ha
          · rw [max_eq_right ha]; nlinarith
          · rw [max_eq_left ha]; nlinarith
        linarith
    · simp only [hev, Bool.false_eq_true, ite_false]
      push_cast
      have := abs_le.mp (show |(a : ℝ) * m 0| ≤ |(a : ℝ)| by
        rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) hm0)
      rw [habs] at this
      constructor <;> linarith

lemma peval_cons (a : ℤ) (as : List ℤ) (x y : ℝ) :
    peval (a :: as) x y = a + ∑ i ∈ range 44, (cf as i : ℝ) * mono (i + 1) x y := by
  rw [peval, NM, sum_range_succ']
  simp only [cf_cons_succ, cf_cons_zero, mono_zero, mul_one]
  ring

theorem rng_spec {t : TM} {f : ℝ → ℝ → ℝ} (ht : t.Encl f) {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    (t.rng.1 : ℝ) ≤ ONE * f x y ∧ (ONE : ℝ) * f x y ≤ t.rng.2 := by
  obtain ⟨h1, h2⟩ := ht x y hx hy
  unfold TM.rng
  match hc : t.c with
  | [] =>
    rw [hc] at h1 h2
    simp only [peval, cf_nil, Int.cast_zero, zero_mul, sum_const_zero, sub_zero] at h1 h2
    exact ⟨h1, h2⟩
  | a :: as =>
    rw [hc] at h1 h2
    have hsp := rngAux_spec as EVEN.tail (fun i => mono (i + 1) x y)
      (fun i _ => mono_abs_le hx hy (i + 1))
      (fun i hi he => by
        obtain ⟨e1, e2⟩ := EVEN_spec i (by rwa [EVEN_tail_length] at hi) he
        simp only [mono]
        exact mul_nonneg (Even.pow_nonneg (Nat.even_iff.mpr e1) _)
          (Even.pow_nonneg (Nat.even_iff.mpr e2) _))
    rw [EVEN_tail_length] at hsp
    rw [peval_cons] at h1 h2
    obtain ⟨s1, s2⟩ := hsp
    simp only
    push_cast
    constructor <;> linarith

theorem absmax_spec {t : TM} {f : ℝ → ℝ → ℝ} (ht : t.Encl f) {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    |(ONE : ℝ) * f x y| ≤ t.absmax := by
  obtain ⟨h1, h2⟩ := rng_spec ht hx hy
  unfold TM.absmax
  rw [abs_le]
  have e1 : ((t.rng.1.natAbs : ℕ) : ℝ) = |(t.rng.1 : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
  have e2 : ((t.rng.2.natAbs : ℕ) : ℝ) = |(t.rng.2 : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
  have m1 : ((t.rng.1.natAbs : ℕ) : ℝ) ≤ ((max t.rng.1.natAbs t.rng.2.natAbs : ℕ) : ℝ) := by
    exact_mod_cast le_max_left _ _
  have m2 : ((t.rng.2.natAbs : ℕ) : ℝ) ≤ ((max t.rng.1.natAbs t.rng.2.natAbs : ℕ) : ℝ) := by
    exact_mod_cast le_max_right _ _
  constructor
  · have := neg_abs_le (t.rng.1 : ℝ); linarith
  · have := le_abs_self (t.rng.2 : ℝ); linarith

/-! ## Rational scaling -/

lemma mulq_poly (q : ℚ) (c : List ℤ) (x y : ℝ) (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    |(q : ℝ) * peval c x y - peval (c.map (fun a => q.num * a / (q.den : ℤ))) x y| ≤ NM := by
  have hd : (0 : ℤ) < q.den := by exact_mod_cast q.den_pos
  have hq : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by exact_mod_cast (Rat.num_div_den q).symm
  have hdR : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  rw [peval, peval, mul_sum, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ i ∈ range NM, |(q : ℝ) * ((cf c i : ℝ) * mono i x y) -
      (cf (c.map (fun a => q.num * a / (q.den : ℤ))) i : ℝ) * mono i x y| ≤ 1 := by
    intro i _
    rw [cf_map (by simp)]
    obtain ⟨b1, b2⟩ := TM.ediv_bounds (q.num * cf c i) q.den hd
    set r := ((q.num * cf c i / (q.den : ℤ) : ℤ) : ℝ)
    have e : (q : ℝ) * ((cf c i : ℝ) * mono i x y) - r * mono i x y =
        ((q.num * cf c i : ℤ) / (q.den : ℝ) - r) * mono i x y := by
      rw [hq]; push_cast; ring
    rw [e, abs_mul]
    have h0 : 0 ≤ ((q.num * cf c i : ℤ) : ℝ) / q.den - r := by
      rw [sub_nonneg, le_div_iff₀ hdR]; push_cast at b1 ⊢; linarith
    have h1 : ((q.num * cf c i : ℤ) : ℝ) / q.den - r ≤ 1 := by
      rw [sub_le_iff_le_add, div_le_iff₀ hdR]; push_cast at b2 ⊢; linarith
    calc |((q.num * cf c i : ℤ) : ℝ) / q.den - r| * |mono i x y| ≤ 1 * 1 :=
          mul_le_mul (by rw [abs_of_nonneg h0]; exact h1) (mono_abs_le hx hy i) (abs_nonneg _)
            zero_le_one
      _ = 1 := one_mul 1
  refine (sum_le_sum this).trans ?_
  simp [NM]

namespace TM

theorem mulq_encl (q : ℚ) {t : TM} {f : ℝ → ℝ → ℝ} (ht : t.Encl f) :
    (t.mulq q).Encl (fun x y => (q : ℝ) * f x y) := by
  intro x y hx hy
  obtain ⟨h1, h2⟩ := ht x y hx hy
  have hp := abs_le.mp (mulq_poly q t.c x y hx hy)
  have hd : (0 : ℤ) < q.den := by exact_mod_cast q.den_pos
  have hdR : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  have hq : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by exact_mod_cast (Rat.num_div_den q).symm
  set e := (ONE : ℝ) * f x y - peval t.c x y with he
  set D := (q : ℝ) * peval t.c x y - peval (t.c.map (fun a => q.num * a / (q.den : ℤ))) x y
  have key : (ONE : ℝ) * ((q : ℝ) * f x y) - peval (t.c.map (fun a => q.num * a / (q.den : ℤ))) x y =
      (q : ℝ) * e + D := by simp only [he, D]; ring
  dsimp only [mulq]
  split_ifs with hn
  · simp only
    rw [key]
    have hq0 : (0 : ℝ) ≤ q := by rw [hq]; exact div_nonneg (by exact_mod_cast hn) hdR.le
    obtain ⟨l1, _⟩ := ediv_bounds (q.num * t.lo) q.den hd
    have l2 := cdiv_bounds (q.num * t.hi) q.den hd
    have m1 : ((q.num * t.lo / (q.den : ℤ) : ℤ) : ℝ) ≤ (q : ℝ) * t.lo := by
      rw [hq, div_mul_eq_mul_div, le_div_iff₀ hdR]; push_cast at l1 ⊢; linarith
    have m2 : (q : ℝ) * t.hi ≤ (cdiv (q.num * t.hi) q.den : ℝ) := by
      rw [hq, div_mul_eq_mul_div, div_le_iff₀ hdR]; push_cast at l2 ⊢; linarith
    have := mul_le_mul_of_nonneg_left h1 hq0
    have := mul_le_mul_of_nonneg_left h2 hq0
    push_cast
    constructor <;> linarith
  · simp only
    rw [key]
    have hq0 : (q : ℝ) ≤ 0 := by
      rw [hq]; exact div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast (not_le.mp hn).le) hdR.le
    obtain ⟨l1, _⟩ := ediv_bounds (q.num * t.hi) q.den hd
    have l2 := cdiv_bounds (q.num * t.lo) q.den hd
    have m1 : ((q.num * t.hi / (q.den : ℤ) : ℤ) : ℝ) ≤ (q : ℝ) * t.hi := by
      rw [hq, div_mul_eq_mul_div, le_div_iff₀ hdR]; push_cast at l1 ⊢; linarith
    have m2 : (q : ℝ) * t.lo ≤ (cdiv (q.num * t.lo) q.den : ℝ) := by
      rw [hq, div_mul_eq_mul_div, div_le_iff₀ hdR]; push_cast at l2 ⊢; linarith
    have := mul_le_mul_of_nonpos_left h2 hq0
    have := mul_le_mul_of_nonpos_left h1 hq0
    push_cast
    constructor <;> linarith

theorem mulI_encl (a b : ℚ) {t : TM} {f : ℝ → ℝ → ℝ} (ht : t.Encl f) {s : ℝ}
    (hs : (a : ℝ) ≤ s ∧ s ≤ b) : (t.mulI a b).Encl (fun x y => s * f x y) := by
  unfold mulI
  refine widen_encl (mulq_encl ((a + b) / 2) ht) _ (fun x y hx hy => ?_)
  have hm := absmax_spec ht hx hy
  have hr : |s - (((a + b) / 2 : ℚ) : ℝ)| ≤ (((b - a) / 2 : ℚ) : ℝ) := by
    push_cast; rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
  have hc := le_qceil_real ((b - a) / 2 * t.absmax)
  push_cast at hc hr ⊢
  calc |(ONE : ℝ) * (s * f x y - ((a : ℝ) + b) / 2 * f x y)|
      = |s - ((a : ℝ) + b) / 2| * |(ONE : ℝ) * f x y| := by rw [← abs_mul]; ring_nf
    _ ≤ ((b : ℝ) - a) / 2 * t.absmax := mul_le_mul hr hm (abs_nonneg _) (by linarith [abs_nonneg (s - ((a : ℝ) + b) / 2)])
    _ ≤ _ := hc

/-- the rounding error of `qfloor` is in `[0, e]` with `e = 0` when exact and `1` otherwise -/
lemma qfloor_err (z : ℚ) :
    0 ≤ (z : ℝ) - qfloor z ∧ (z : ℝ) - qfloor z ≤ ((if (qfloor z : ℚ) = z then 0 else 1 : ℤ) : ℝ) := by
  have h1 := qfloor_le_real z
  have h2 := lt_qfloor_add_one_real z
  refine ⟨by linarith, ?_⟩
  split_ifs with h
  · have : ((qfloor z : ℚ) : ℝ) = (z : ℝ) := by rw [h]
    push_cast at this ⊢; linarith
  · push_cast; linarith

theorem affine_encl (mid rad : ℚ) (var : ℕ) :
    (affine mid rad var).Encl (fun x y => (mid : ℝ) + rad * (if var = 0 then x else y)) := by
  intro x y hx hy
  beta_reduce
  have hv : |(if var = 0 then x else y)| ≤ 1 := by split_ifs <;> assumption
  obtain ⟨a0, b0⟩ := qfloor_err (mid * ONE)
  obtain ⟨a1, b1⟩ := qfloor_err (rad * ONE)
  push_cast at a0 b0 a1 b1
  have hp : peval (affine mid rad var).c x y =
      (qfloor (mid * ONE) : ℝ) + (qfloor (rad * ONE) : ℝ) * (if var = 0 then x else y) := by
    unfold affine
    split_ifs with h
    · rw [peval, NM]; simp [sum_range_succ, cf, mono, mx, MONO]
    · rw [peval, NM]; simp [sum_range_succ, cf, mono, mx, MONO]
  rw [hp]
  generalize (if var = 0 then x else y) = v at hv ⊢
  have bv : |((rad : ℝ) * ONE - qfloor (rad * ONE)) * v| ≤ (rad : ℝ) * ONE - qfloor (rad * ONE) := by
    rw [abs_mul, abs_of_nonneg a1]; exact mul_le_of_le_one_right a1 hv
  have bva := abs_le.mp bv
  have key : (ONE : ℝ) * ((mid : ℝ) + rad * v) - ((qfloor (mid * ONE) : ℝ) + (qfloor (rad * ONE) : ℝ) * v) =
      ((mid : ℝ) * ONE - qfloor (mid * ONE)) + ((rad : ℝ) * ONE - qfloor (rad * ONE)) * v := by ring
  rw [key]
  unfold affine
  dsimp only
  push_cast
  constructor <;> linarith

theorem center_encl {t : TM} {f : ℝ → ℝ → ℝ} (ht : t.Encl f) :
    t.center.2.Encl (fun x y => f x y - (t.center.1 : ℝ) / ONE) := by
  obtain ⟨c, lo, hi⟩ := t
  intro x y hx hy
  obtain ⟨h1, h2⟩ := ht x y hx hy
  beta_reduce
  cases c with
  | nil =>
    simp only [center, Int.cast_zero, zero_div, sub_zero]
    exact ⟨h1, h2⟩
  | cons a as =>
    simp only [center] at h1 h2 ⊢
    rw [peval_cons] at h1 h2 ⊢
    have : (ONE : ℝ) * ((a : ℝ) / ONE) = a := by
      rw [mul_div_assoc']; exact mul_div_cancel_left₀ _ ONE_pos.ne'
    push_cast
    constructor <;> nlinarith

end TM

end OM.NNN20
