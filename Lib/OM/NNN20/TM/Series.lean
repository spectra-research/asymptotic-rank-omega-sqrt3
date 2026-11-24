import Lib.OM.NNN20.TM.Kron
import Lib.OM.NNN20.TM.Scalar

/-! # Reciprocal, logarithm and exponential of Taylor models

With `c = c0 / ONE` the constant coefficient of `t`:

* `recip_encl`: `f = c (1 - u)`, `|u| ≤ M < 1`, `1/f = (1/c)(Σ_{k ≤ n} u^k + u^(n+1)/(1-u))`.
* `log2_encl`: `f = c (1 + u)`, `log f = log c + Σ_{i=1}^n (-1)^(i+1) u^i / i + R`,
  `|R| ≤ M^(n+1) / ((n+1)(1-M))` (`log_tail`, from `Real.hasSum_pow_div_log_of_abs_lt_one`),
  then `logb 2 = log / log 2` with `1/log 2 ∈ [1/LN2HI, 1/LN2LO]`.
* `exp2_encl`: `2^f = 2^c exp v`, `v = (f - c) log 2`, `|v| ≤ 1`, `Real.exp_bound`. -/

namespace OM.NNN20

open Finset

/-! ## The tail of the logarithm series -/

theorem log_tail {u : ℝ} (hu : |u| < 1) (n : ℕ) :
    |Real.log (1 + u) - ∑ k ∈ range n, (-1) ^ k * u ^ (k + 1) / (k + 1)| ≤
      |u| ^ (n + 1) / ((n + 1) * (1 - |u|)) := by
  set F : ℕ → ℝ := fun k => (-u) ^ (k + 1) / (k + 1)
  have hu' : |-u| < 1 := by rwa [abs_neg]
  have hF := Real.hasSum_pow_div_log_of_abs_lt_one hu'
  rw [sub_neg_eq_add] at hF
  have hsum := hF.summable
  have htail := hsum.sum_add_tsum_nat_add n
  rw [hF.tsum_eq] at htail
  have hpart : ∑ k ∈ range n, (-1) ^ k * u ^ (k + 1) / (k + 1) = -∑ k ∈ range n, F k := by
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun k _ => ?_
    simp only [F, neg_pow (u), pow_succ (-1 : ℝ)]
    ring
  have key : Real.log (1 + u) - ∑ k ∈ range n, (-1) ^ k * u ^ (k + 1) / (k + 1) =
      -∑' k, F (k + n) := by
    rw [hpart]; linarith
  rw [key, abs_neg]
  have hau : 0 ≤ |u| := abs_nonneg u
  have hgeo := summable_geometric_of_lt_one hau hu
  have hbd : ∀ k, ‖F (k + n)‖ ≤ |u| ^ (n + 1) / (n + 1) * |u| ^ k := by
    intro k
    simp only [F, Real.norm_eq_abs, abs_div, abs_pow, abs_neg]
    have h1 : (0 : ℝ) < (k + n : ℕ) + 1 := by positivity
    rw [abs_of_pos h1, div_le_iff₀ h1]
    have : |u| ^ (k + n + 1) = |u| ^ (n + 1) * |u| ^ k := by rw [← pow_add]; ring_nf
    rw [this]
    have hn : ((n : ℝ) + 1) ≤ (k + n : ℕ) + 1 := by push_cast; linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
    have h0 : 0 ≤ |u| ^ (n + 1) * |u| ^ k := by positivity
    calc |u| ^ (n + 1) * |u| ^ k = |u| ^ (n + 1) / (n + 1) * |u| ^ k * (n + 1) := by field_simp
      _ ≤ |u| ^ (n + 1) / (n + 1) * |u| ^ k * ((k + n : ℕ) + 1) := by gcongr
  have hsumb : Summable (fun k => |u| ^ (n + 1) / (n + 1) * |u| ^ k) := hgeo.mul_left _
  have hnorm : Summable (fun k => ‖F (k + n)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbd hsumb
  calc |∑' k, F (k + n)| = ‖∑' k, F (k + n)‖ := rfl
    _ ≤ ∑' k, ‖F (k + n)‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' k, |u| ^ (n + 1) / (n + 1) * |u| ^ k := hnorm.tsum_le_tsum hbd hsumb
    _ = |u| ^ (n + 1) / (n + 1) * (1 - |u|)⁻¹ := by
        rw [hgeo.tsum_mul_left, tsum_geometric_of_lt_one hau hu]
    _ = _ := by field_simp

namespace TM

lemma const_one_encl : (const ONE).Encl (fun _ _ => 1) :=
  (const_encl ONE).congr fun _ _ _ _ => div_self ONE_pos.ne'

/-! ## The reciprocal -/

lemma recipSeries_encl {q : TM} {u : ℝ → ℝ → ℝ} (hq : q.Encl u) :
    ∀ (k m : ℕ) (term out : TM), term.Encl (fun x y => u x y ^ m) →
      out.Encl (fun x y => ∑ j ∈ range (m + 1), u x y ^ j) →
      (recipSeries q k term out).Encl (fun x y => ∑ j ∈ range (m + k + 1), u x y ^ j)
  | 0, m, term, out, _, hout => by simpa [recipSeries] using hout
  | k + 1, m, term, out, hterm, hout => by
    rw [recipSeries]
    have ht' : (term.mul q).Encl (fun x y => u x y ^ (m + 1)) :=
      (mul_encl hterm hq).congr fun x y _ _ => by ring
    have ho' : (out.add (term.mul q)).Encl (fun x y => ∑ j ∈ range (m + 1 + 1), u x y ^ j) :=
      (add_encl hout ht').congr fun x y _ _ => by rw [sum_range_succ (n := m + 1)]
    have := recipSeries_encl hq k (m + 1) _ _ ht' ho'
    simpa [show m + 1 + k + 1 = m + (k + 1) + 1 by omega] using this

theorem recip_encl {t : TM} {f : ℝ → ℝ → ℝ} (ht : t.Encl f) {r : TM} (hr : t.recip = some r) :
    r.Encl (fun x y => 1 / f x y) := by
  unfold recip at hr
  dsimp only at hr
  split_ifs at hr with h0 h1
  cases hr
  have hO : (ONE : ℝ) ≠ 0 := ONE_pos.ne'
  have hd := center_encl ht
  have hc0 : (t.center.1 : ℝ) ≠ 0 := by exact_mod_cast h0
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = (t.center.1 : ℝ) / ONE := ⟨_, rfl⟩
  have hc : c ≠ 0 := by rw [hcdef]; exact div_ne_zero hc0 hO
  -- u = 1 - f / c
  have hq : (t.center.2.mulq ((-ONE : ℚ) / t.center.1)).Encl
      (fun x y => (((-ONE : ℚ) / t.center.1 : ℚ) : ℝ) * (f x y - t.center.1 / ONE)) :=
    mulq_encl _ hd
  set u : ℝ → ℝ → ℝ := fun x y => (((-ONE : ℚ) / t.center.1 : ℚ) : ℝ) * (f x y - t.center.1 / ONE)
  have hu_eq : ∀ x y, u x y = 1 - f x y / c := by
    intro x y; simp only [u]; rw [hcdef]; push_cast; field_simp; ring
  obtain ⟨M, hMdef⟩ : ∃ M : ℕ, M = (t.center.2.mulq ((-ONE : ℚ) / t.center.1)).absmax := ⟨_, rfl⟩
  have hM : (M : ℤ) < ONE := by rw [hMdef]; exact not_le.mp h1
  obtain ⟨Mq, hMqdef⟩ : ∃ Mq : ℝ, Mq = (M : ℝ) / ONE := ⟨_, rfl⟩
  have hMq1 : Mq < 1 := by
    rw [hMqdef, div_lt_one ONE_pos]; exact_mod_cast hM
  have hMq0 : 0 ≤ Mq := by rw [hMqdef]; exact div_nonneg (Nat.cast_nonneg _) ONE_pos.le
  have hub : ∀ x y, |x| ≤ 1 → |y| ≤ 1 → |u x y| ≤ Mq := by
    intro x y hx hy
    have := absmax_spec hq hx hy
    rw [← hMdef] at this
    rw [hMqdef, le_div_iff₀ ONE_pos]
    rw [abs_mul, abs_of_pos ONE_pos] at this; linarith [mul_comm (ONE : ℝ) |u x y|]
  -- the series
  have hser := recipSeries_encl hq NS 0 (const ONE) (const ONE)
    (const_one_encl.congr fun _ _ _ _ => (pow_zero _).symm)
    (const_one_encl.congr fun _ _ _ _ => by simp)
  have hout := mulq_encl ((ONE : ℚ) / t.center.1) hser
  refine widen_encl hout _ fun x y hx hy => ?_
  have hu := hub x y hx hy
  have hu1 : |u x y| < 1 := lt_of_le_of_lt hu hMq1
  have hne : 1 - u x y ≠ 0 := by
    have := (abs_lt.mp hu1).2; linarith
  have hf : f x y = c * (1 - u x y) := by rw [hu_eq]; field_simp; ring
  have hgeom : 1 / (1 - u x y) - ∑ j ∈ range (0 + NS + 1), u x y ^ j =
      u x y ^ (NS + 1) / (1 - u x y) := by
    have := mul_neg_geom_sum (u x y) (NS + 1)
    rw [zero_add]
    field_simp
    linarith
  have e : 1 / f x y - (((ONE : ℚ) / t.center.1 : ℚ) : ℝ) * ∑ j ∈ range (0 + NS + 1), u x y ^ j =
      (1 / c) * (u x y ^ (NS + 1) / (1 - u x y)) := by
    rw [hf, ← hgeom]
    have : (((ONE : ℚ) / t.center.1 : ℚ) : ℝ) = 1 / c := by rw [hcdef]; push_cast; field_simp
    rw [this]; field_simp
  rw [e]
  have hcpos : 0 < |c| := abs_pos.mpr hc
  have h3 : 0 < 1 - Mq := by linarith
  have hbound : |(1 / c) * (u x y ^ (NS + 1) / (1 - u x y))| ≤ Mq ^ (NS + 1) / (1 - Mq) / |c| := by
    have h1 : |u x y| ^ (NS + 1) ≤ Mq ^ (NS + 1) := pow_le_pow_left₀ (abs_nonneg _) hu _
    have h2 : 1 - Mq ≤ |1 - u x y| := by
      have := (abs_le.mp hu).2
      calc 1 - Mq ≤ 1 - u x y := by linarith
        _ ≤ |1 - u x y| := le_abs_self _
    have e2 : |(1 / c) * (u x y ^ (NS + 1) / (1 - u x y))| =
        |u x y| ^ (NS + 1) / (|1 - u x y| * |c|) := by
      rw [abs_mul, abs_div, abs_div, abs_one, abs_pow]; field_simp
    rw [e2, div_div]
    apply div_le_div₀ (by positivity) h1 (by positivity)
    exact mul_le_mul_of_nonneg_right h2 hcpos.le
  have hceil := le_qceil_real (((M : ℚ) / ONE) ^ (NS + 1) / (1 - (M : ℚ) / ONE) /
    |((t.center.1 : ℚ) / ONE)| * ONE)
  push_cast at hceil
  rw [abs_mul, abs_of_pos ONE_pos]
  calc (ONE : ℝ) * |1 / c * (u x y ^ (NS + 1) / (1 - u x y))|
      ≤ ONE * (Mq ^ (NS + 1) / (1 - Mq) / |c|) := mul_le_mul_of_nonneg_left hbound ONE_pos.le
    _ = ((M : ℝ) / ONE) ^ (NS + 1) / (1 - (M : ℝ) / ONE) / |(t.center.1 : ℝ) / ONE| * ONE := by
        rw [hMqdef, hcdef]; ring
    _ ≤ _ := by rw [← hMdef]; exact hceil

/-! ## The logarithm -/

lemma logSeries_encl {q : TM} {u : ℝ → ℝ → ℝ} (hq : q.Encl u) :
    ∀ (k i : ℕ) (term out : TM), 1 ≤ i → term.Encl (fun x y => u x y ^ i) →
      out.Encl (fun x y => ∑ j ∈ range i, (-1) ^ j * u x y ^ (j + 1) / (j + 1)) →
      (logSeries q k (i + 1) term out).Encl
        (fun x y => ∑ j ∈ range (i + k), (-1) ^ j * u x y ^ (j + 1) / (j + 1))
  | 0, i, term, out, _, _, hout => by simpa [logSeries] using hout
  | k + 1, i, term, out, hi, hterm, hout => by
    rw [logSeries]
    have ht' : (term.mul q).Encl (fun x y => u x y ^ (i + 1)) :=
      (mul_encl hterm hq).congr fun x y _ _ => by ring
    have hc := mulq_encl ((-1) ^ (i + 1 + 1) / ((i + 1 : ℕ) : ℚ)) ht'
    have ho' : (out.add (mulq ((-1) ^ (i + 1 + 1) / ((i + 1 : ℕ) : ℚ)) (term.mul q))).Encl
        (fun x y => ∑ j ∈ range (i + 1), (-1) ^ j * u x y ^ (j + 1) / (j + 1)) :=
      (add_encl hout hc).congr fun x y _ _ => by
        rw [sum_range_succ]; push_cast; ring
    have := logSeries_encl hq k (i + 1) _ _ (by omega) ht' ho'
    simpa [show i + 1 + k = i + (k + 1) by omega] using this

theorem log2_encl {t : TM} {f : ℝ → ℝ → ℝ} (ht : t.Encl f) {r : TM} (hr : t.log2 = some r) :
    (∀ x y, |x| ≤ 1 → |y| ≤ 1 → 0 < f x y) ∧ r.Encl (fun x y => Real.logb 2 (f x y)) := by
  unfold log2 at hr
  dsimp only at hr
  split_ifs at hr with h0 h1
  split at hr
  · cases hr
  rename_i l hl
  cases hr
  have hO : (ONE : ℝ) ≠ 0 := ONE_pos.ne'
  have hd := center_encl ht
  have hc0 : (0 : ℝ) < t.center.1 := by exact_mod_cast (not_le.mp h0)
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = (t.center.1 : ℝ) / ONE := ⟨_, rfl⟩
  have hcp : 0 < c := by rw [hcdef]; exact div_pos hc0 ONE_pos
  have hq : (t.center.2.mulq ((ONE : ℚ) / t.center.1)).Encl
      (fun x y => (((ONE : ℚ) / t.center.1 : ℚ) : ℝ) * (f x y - t.center.1 / ONE)) :=
    mulq_encl _ hd
  set u : ℝ → ℝ → ℝ := fun x y => (((ONE : ℚ) / t.center.1 : ℚ) : ℝ) * (f x y - t.center.1 / ONE)
  have hu_eq : ∀ x y, f x y = c * (1 + u x y) := by
    intro x y; simp only [u]; rw [hcdef]; push_cast; field_simp; ring
  obtain ⟨M, hMdef⟩ : ∃ M : ℕ, M = (t.center.2.mulq ((ONE : ℚ) / t.center.1)).absmax := ⟨_, rfl⟩
  have hM : (M : ℤ) < ONE := by rw [hMdef]; exact not_le.mp h1
  obtain ⟨Mq, hMqdef⟩ : ∃ Mq : ℝ, Mq = (M : ℝ) / ONE := ⟨_, rfl⟩
  have hMq1 : Mq < 1 := by rw [hMqdef, div_lt_one ONE_pos]; exact_mod_cast hM
  have hMq0 : 0 ≤ Mq := by rw [hMqdef]; exact div_nonneg (Nat.cast_nonneg _) ONE_pos.le
  have hub : ∀ x y, |x| ≤ 1 → |y| ≤ 1 → |u x y| ≤ Mq := by
    intro x y hx hy
    have := absmax_spec hq hx hy
    rw [← hMdef] at this
    rw [hMqdef, le_div_iff₀ ONE_pos]
    rw [abs_mul, abs_of_pos ONE_pos] at this; linarith [mul_comm (ONE : ℝ) |u x y|]
  have hfpos : ∀ x y, |x| ≤ 1 → |y| ≤ 1 → 0 < f x y := by
    intro x y hx hy
    rw [hu_eq]
    have := (abs_le.mp (hub x y hx hy)).1
    exact mul_pos hcp (by linarith)
  refine ⟨hfpos, ?_⟩
  -- the series and its tail
  have hser := logSeries_encl hq (NS - 1) 1 _ _ le_rfl
    (hq.congr fun _ _ _ _ => (pow_one _).symm)
    (hq.congr fun x y _ _ => by simp)
  have hser' : (logSeries (t.center.2.mulq ((ONE : ℚ) / t.center.1)) (NS - 1) 2
      (t.center.2.mulq ((ONE : ℚ) / t.center.1)) (t.center.2.mulq ((ONE : ℚ) / t.center.1))).Encl
      (fun x y => ∑ j ∈ range NS, (-1) ^ j * u x y ^ (j + 1) / (j + 1)) := by
    simpa [show 1 + (NS - 1) = NS by simp [NS]] using hser
  have hlogc := logI_spec hl
  -- log f = log c + log(1 + u)
  have hw := widen_encl hser' (qceil (((M : ℚ) / ONE) ^ (NS + 1) / (1 - (M : ℚ) / ONE) /
      (NS + 1 : ℕ) * ONE))
    (g := fun x y => Real.log (1 + u x y)) (fun x y hx hy => by
      have hu := hub x y hx hy
      have hu1 : |u x y| < 1 := lt_of_le_of_lt hu hMq1
      have htl := log_tail hu1 NS
      have hceil := le_qceil_real (((M : ℚ) / ONE) ^ (NS + 1) / (1 - (M : ℚ) / ONE) /
        (NS + 1 : ℕ) * ONE)
      push_cast at hceil
      rw [abs_mul, abs_of_pos ONE_pos]
      have h3 : 0 < 1 - Mq := by linarith
      have hb : |u x y| ^ (NS + 1) / ((NS + 1) * (1 - |u x y|)) ≤ Mq ^ (NS + 1) / ((NS + 1) * (1 - Mq)) := by
        apply div_le_div₀ (pow_nonneg hMq0 _) (pow_le_pow_left₀ (abs_nonneg _) hu _)
          (mul_pos (by positivity) h3)
        gcongr
      calc (ONE : ℝ) * |Real.log (1 + u x y) - ∑ j ∈ range NS, (-1) ^ j * u x y ^ (j + 1) / (j + 1)|
          ≤ ONE * (Mq ^ (NS + 1) / ((NS + 1) * (1 - Mq))) :=
            mul_le_mul_of_nonneg_left (htl.trans hb) ONE_pos.le
        _ = ((M : ℝ) / ONE) ^ (NS + 1) / (1 - (M : ℝ) / ONE) / ((NS : ℝ) + 1) * ONE := by
            rw [hMqdef]; field_simp
        _ ≤ _ := by push_cast; exact hceil)
  have hlog := add_encl hw (constI_encl l.1 l.2 (f := fun _ _ => Real.log c) (fun _ _ _ _ => by
    rw [hcdef]; push_cast at hlogc ⊢; exact hlogc))
  have hl2 := ln2_bounds
  have hs : ((1 / LN2HI : ℚ) : ℝ) ≤ 1 / Real.log 2 ∧ 1 / Real.log 2 ≤ ((1 / LN2LO : ℚ) : ℝ) := by
    have h0 := LN2LO_pos
    push_cast
    exact ⟨one_div_le_one_div_of_le (by linarith) hl2.2, one_div_le_one_div_of_le h0 hl2.1⟩
  subst hMdef
  refine (mulI_encl _ _ hlog hs).congr fun x y hx hy => ?_
  rw [Real.logb, hu_eq x y, Real.log_mul hcp.ne' (by
    have := (abs_le.mp (hub x y hx hy)).1; linarith)]
  ring

/-! ## The exponential -/

lemma expSeries_encl {q : TM} {v : ℝ → ℝ → ℝ} (hq : q.Encl v) :
    ∀ (k i : ℕ) (term out : TM), 1 ≤ i →
      term.Encl (fun x y => v x y ^ (i - 1) / ((i - 1).factorial : ℝ)) →
      out.Encl (fun x y => ∑ j ∈ range i, v x y ^ j / (j.factorial : ℝ)) →
      (expSeries q k i term out).Encl (fun x y => ∑ j ∈ range (i + k), v x y ^ j / (j.factorial : ℝ))
  | 0, i, term, out, _, _, hout => by simpa [expSeries] using hout
  | k + 1, i, term, out, hi, hterm, hout => by
    rw [expSeries]
    have ht' : (mulq (1 / (i : ℚ)) (term.mul q)).Encl (fun x y => v x y ^ i / (i.factorial : ℝ)) :=
      (mulq_encl _ (mul_encl hterm hq)).congr fun x y _ _ => by
        obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
        simp only [Nat.add_sub_cancel, Nat.factorial_succ]
        push_cast
        field_simp
        ring
    have ho' : (out.add (mulq (1 / (i : ℚ)) (term.mul q))).Encl
        (fun x y => ∑ j ∈ range (i + 1), v x y ^ j / (j.factorial : ℝ)) :=
      (add_encl hout ht').congr fun x y _ _ => by rw [sum_range_succ]
    have := expSeries_encl hq k (i + 1) _ _ (by omega)
      (by simpa using ht') ho'
    simpa [show i + 1 + k = i + (k + 1) by omega] using this

theorem exp2_encl {t : TM} {f : ℝ → ℝ → ℝ} (ht : t.Encl f) {r : TM} (hr : t.exp2 = some r) :
    r.Encl (fun x y => (2 : ℝ) ^ f x y) := by
  unfold exp2 at hr
  dsimp only at hr
  split_ifs at hr with h1
  cases hr
  have hO : (ONE : ℝ) ≠ 0 := ONE_pos.ne'
  have hd := center_encl ht
  have hl2 := ln2_bounds
  have hq := mulI_encl LN2LO LN2HI hd hl2
  set v : ℝ → ℝ → ℝ := fun x y => Real.log 2 * (f x y - t.center.1 / ONE)
  obtain ⟨M, hMdef⟩ : ∃ M : ℕ, M = (t.center.2.mulI LN2LO LN2HI).absmax := ⟨_, rfl⟩
  have hM : (M : ℤ) ≤ ONE := by rw [hMdef]; exact not_lt.mp h1
  obtain ⟨Mq, hMqdef⟩ : ∃ Mq : ℝ, Mq = (M : ℝ) / ONE := ⟨_, rfl⟩
  have hMq1 : Mq ≤ 1 := by rw [hMqdef, div_le_one ONE_pos]; exact_mod_cast hM
  have hvb : ∀ x y, |x| ≤ 1 → |y| ≤ 1 → |v x y| ≤ Mq := by
    intro x y hx hy
    have := absmax_spec hq hx hy
    rw [← hMdef] at this
    rw [hMqdef, le_div_iff₀ ONE_pos]
    rw [abs_mul, abs_of_pos ONE_pos] at this; linarith [mul_comm (ONE : ℝ) |v x y|]
  have hser := expSeries_encl hq NS 1 (const ONE) (const ONE) le_rfl
    (const_one_encl.congr fun _ _ _ _ => by simp)
    (const_one_encl.congr fun _ _ _ _ => by simp)
  have hw := widen_encl hser (qceil (((M : ℚ) / ONE) ^ (NS + 1) * (NS + 2 : ℕ) /
      ((Nat.factorial (NS + 1) : ℚ) * (NS + 1 : ℕ)) * ONE))
    (g := fun x y => Real.exp (v x y)) (fun x y hx hy => by
      have hv := hvb x y hx hy
      have hb := Real.exp_bound (hv.trans hMq1) (show 0 < NS + 1 by omega)
      have hceil := le_qceil_real (((M : ℚ) / ONE) ^ (NS + 1) * (NS + 2 : ℕ) /
        ((Nat.factorial (NS + 1) : ℚ) * (NS + 1 : ℕ)) * ONE)
      push_cast at hceil
      rw [abs_mul, abs_of_pos ONE_pos]
      have hpow : |v x y| ^ (NS + 1) ≤ Mq ^ (NS + 1) := pow_le_pow_left₀ (abs_nonneg _) hv _
      calc (ONE : ℝ) * |Real.exp (v x y) - ∑ j ∈ range (1 + NS), v x y ^ j / (j.factorial : ℝ)|
          = ONE * |Real.exp (v x y) - ∑ j ∈ range (NS + 1), v x y ^ j / (j.factorial : ℝ)| := by
            rw [add_comm 1 NS]
        _ ≤ ONE * (|v x y| ^ (NS + 1) * (((NS + 1).succ : ℕ) / (((NS + 1).factorial : ℕ) *
              ((NS + 1 : ℕ) : ℝ)))) :=
            mul_le_mul_of_nonneg_left hb ONE_pos.le
        _ ≤ ONE * (Mq ^ (NS + 1) * (((NS + 1).succ : ℕ) / (((NS + 1).factorial : ℕ) *
              ((NS + 1 : ℕ) : ℝ)))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow (by positivity)) ONE_pos.le
        _ = ((M : ℝ) / ONE) ^ (NS + 1) * ((NS : ℝ) + 2) / (((NS + 1).factorial : ℝ) * ((NS : ℝ) + 1)) * ONE := by
            rw [hMqdef]; push_cast; ring
        _ ≤ _ := by push_cast; exact hceil)
  have he := exp2I_spec ((t.center.1 : ℚ) / ONE)
  subst hMdef
  refine (mulI_encl _ _ hw (s := (2 : ℝ) ^ (((t.center.1 : ℚ) / ONE : ℚ) : ℝ)) he).congr
    fun x y _ _ => ?_
  simp only [v]
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), ← Real.exp_add]
  congr 1
  push_cast
  ring

end TM

end OM.NNN20

