import Lib.OM.NNN.Scalar

namespace OM.NNN

noncomputable def retainedSize (n a : ℕ) : ℝ := ((a - 1 : ℕ) : ℝ) * (n : ℝ) ^ 2

/-- The ordinary-block spectral square envelope in P7, equation (17). -/
noncomputable def squaredEnvelope (n : ℕ) (p : List ℕ) (u : ℝ) : ℝ :=
  (n : ℝ) ^ ((9 : ℝ) / 4 + u) + (p.length : ℝ) * ((n : ℝ) ^ 2) ^ u -
    (p.map (fun a => retainedSize n a ^ u)).sum

private lemma block_power_bound (a : ℕ) (ha : 7 ≤ a ∧ a ≤ 16) :
    ((a - 1 : ℕ) : ℝ) ^ ((3 : ℝ) / 4) ≤ (2 / 3 : ℝ) * a := by
  have hc : ∀ a : Fin 17, 7 ≤ a.val → (a.val - 1) ^ 3 * 3 ^ 4 ≤ (2 * a.val) ^ 4 := by
    decide +kernel
  have h := hc ⟨a, by omega⟩ ha.1
  have hR : ((a - 1 : ℕ) : ℝ) ^ 3 * (3 : ℝ) ^ 4 ≤ (2 * (a : ℝ)) ^ 4 := by
    exact_mod_cast h
  apply le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0) (by positivity)
  rw [rpow_three_quarters_pow_four (Nat.cast_nonneg _)]
  nlinarith

private lemma retainedSize_pos {n a : ℕ} (hn : 7 ≤ n) (ha : 7 ≤ a) :
    0 < retainedSize n a := by
  unfold retainedSize
  have hna : 0 < a - 1 := by omega
  have hnn : 0 < n := by omega
  positivity

private lemma retained_deriv_bound (n a : ℕ) (hn : 7 ≤ n)
    (ha : 7 ≤ a ∧ a ≤ 16) (han : a ≤ n) (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) (3 / 4)) :
    Real.log (retainedSize n a) * retainedSize n a ^ u ≤
      2 * Real.log n * (n : ℝ) ^ (2 * u) * a := by
  have hnR : (7 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hb1 : (1 : ℝ) ≤ ((a - 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ a - 1 by omega)
  have hb0 : (0 : ℝ) ≤ ((a - 1 : ℕ) : ℝ) := by positivity
  have hbn : ((a - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast (show a - 1 ≤ n by omega)
  have ht0 := retainedSize_pos hn ha.1
  have hlog : Real.log (retainedSize n a) ≤ 3 * Real.log n := by
    have ht : retainedSize n a ≤ (n : ℝ) ^ (3 : ℕ) := by
      unfold retainedSize
      nlinarith [mul_le_mul_of_nonneg_right hbn (sq_nonneg (n : ℝ))]
    exact (Real.log_le_log ht0 ht).trans_eq (Real.log_pow (n : ℝ) 3)
  have hbpow : ((a - 1 : ℕ) : ℝ) ^ u ≤ (2 / 3 : ℝ) * a :=
    (Real.rpow_le_rpow_of_exponent_le hb1 hu.2).trans (block_power_bound a ha)
  have htform : retainedSize n a ^ u =
      ((a - 1 : ℕ) : ℝ) ^ u * (n : ℝ) ^ (2 * u) := by
    rw [retainedSize, Real.mul_rpow hb0 (sq_nonneg _), ← Real.rpow_natCast_mul hn0.le]
    norm_num
  have hpow := mul_le_mul_of_nonneg_right hbpow (Real.rpow_nonneg hn0.le (2 * u))
  rw [← htform] at hpow
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  calc
    _ ≤ (3 * Real.log n) * retainedSize n a ^ u :=
      mul_le_mul_of_nonneg_right hlog (Real.rpow_nonneg ht0.le _)
    _ ≤ (3 * Real.log n) * ((2 / 3 : ℝ) * a * (n : ℝ) ^ (2 * u)) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := by ring

private lemma hasDerivAt_retained_sum (n : ℕ) (hn : 7 ≤ n) (p : List ℕ)
    (hp : ∀ a ∈ p, 7 ≤ a) (u : ℝ) :
    HasDerivAt (fun v : ℝ => (p.map (fun a => retainedSize n a ^ v)).sum)
      (p.map (fun a => Real.log (retainedSize n a) * retainedSize n a ^ u)).sum u := by
  induction p with
  | nil => simpa using! (hasDerivAt_const u (0 : ℝ))
  | cons a p ih =>
    have ha := (hasDerivAt_id u).const_rpow (retainedSize_pos hn (hp a (by simp)))
    have ht := ih (fun b hb => hp b (by simp [hb]))
    simpa using! ha.add ht

private lemma retained_deriv_sum_bound (n : ℕ) (hn : 7 ≤ n) (p : List ℕ)
    (hp : ∀ a ∈ p, (7 ≤ a ∧ a ≤ 16) ∧ a ≤ n)
    (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) (3 / 4)) :
    (p.map (fun a => Real.log (retainedSize n a) * retainedSize n a ^ u)).sum ≤
      2 * Real.log n * (n : ℝ) ^ (2 * u) * (p.sum : ℝ) := by
  induction p with
  | nil => simp
  | cons a p ih =>
    have ha := hp a (by simp)
    have hd := retained_deriv_bound n a hn ha.1 ha.2 u hu
    have ht := ih (fun b hb => hp b (by simp [hb]))
    simp only [List.map_cons, List.sum_cons, Nat.cast_add]
    nlinarith

private lemma rpow_three_halves (n : ℕ) (hn : 0 < n) :
    (n : ℝ) ^ ((3 : ℝ) / 2) = n * Real.sqrt n := by
  calc
    (n : ℝ) ^ ((3 : ℝ) / 2) = (n : ℝ) ^ (1 + (1 : ℝ) / 2) := by norm_num
    _ = n * Real.sqrt n := by
      rw [Real.rpow_add (by exact_mod_cast hn), Real.rpow_one, Real.sqrt_eq_rpow]

private lemma main_deriv_dominates (n : ℕ) (hn : 7 ≤ n) (u : ℝ) (hu : u ≤ (3 : ℝ) / 4) :
    2 * Real.log n * (n : ℝ) ^ (2 * u) * n ≤
      Real.log n * (n : ℝ) ^ ((9 : ℝ) / 4 + u) := by
  have hnR : (7 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hs2 := Real.sq_sqrt hn0.le
  have hs0 := Real.sqrt_nonneg (n : ℝ)
  have hs : (2 : ℝ) ≤ Real.sqrt n := by nlinarith
  have htwo : (2 : ℝ) * n ≤ (n : ℝ) ^ ((3 : ℝ) / 2) := by
    rw [rpow_three_halves n (by omega)]
    nlinarith
  have hpow := mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hn0.le (2 * u))
  rw [← Real.rpow_add hn0] at hpow
  have he : (n : ℝ) ^ ((3 : ℝ) / 2 + 2 * u) ≤
      (n : ℝ) ^ ((9 : ℝ) / 4 + u) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have h := mul_le_mul_of_nonneg_left (hpow.trans he) (Real.log_nonneg hn1)
  nlinarith

/-- The envelope is nondecreasing on the entire interval used by the omega bound.
The chosen blocks lie in `[7,16]`, allowing the elementary density bound `2/3`. -/
theorem squaredEnvelope_monotone (n : ℕ) (hn : 7 ≤ n) (p : List ℕ)
    (hsum : p.sum = n) (hp : ∀ a ∈ p, 7 ≤ a ∧ a ≤ 16) :
    MonotoneOn (squaredEnvelope n p) (Set.Icc (0 : ℝ) (3 / 4)) := by
  have hnR : (7 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  let df (u : ℝ) := Real.log n * (n : ℝ) ^ ((9 : ℝ) / 4 + u) +
    (p.length : ℝ) * (Real.log ((n : ℝ) ^ 2) * ((n : ℝ) ^ 2) ^ u) -
      (p.map (fun a => Real.log (retainedSize n a) * retainedSize n a ^ u)).sum
  have hd (u : ℝ) : HasDerivAt (squaredEnvelope n p) (df u) u := by
    have hmain := ((hasDerivAt_const u ((9 : ℝ) / 4)).add (hasDerivAt_id u)).const_rpow hn0
    have hcor := ((hasDerivAt_id u).const_rpow (sq_pos_of_pos hn0)).const_mul (p.length : ℝ)
    have hret := hasDerivAt_retained_sum n hn p (fun a ha => (hp a ha).1) u
    simpa [squaredEnvelope, df] using! (hmain.add hcor).sub hret
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
    (fun u _ => (hd u).continuousAt.continuousWithinAt)
    (fun u _ => (hd u).hasDerivWithinAt) ?_
  intro u hu
  have hu' : u ∈ Set.Icc (0 : ℝ) (3 / 4) := interior_subset hu
  have hret := retained_deriv_sum_bound n hn p (fun a ha =>
    ⟨hp a ha, hsum ▸ List.single_le_sum (fun b _ => Nat.zero_le b) a ha⟩) u hu'
  rw [hsum] at hret
  have hmain := main_deriv_dominates n hn u hu'.2
  have hlog : 0 ≤ Real.log ((n : ℝ) ^ 2) := Real.log_nonneg (by nlinarith)
  have hcor : 0 ≤ (p.length : ℝ) *
      (Real.log ((n : ℝ) ^ 2) * ((n : ℝ) ^ 2) ^ u) := by positivity
  dsimp [df]
  linarith

private lemma retainedSize_endpoint (n a : ℕ) :
    retainedSize n a ^ ((3 : ℝ) / 4) =
      (n : ℝ) ^ ((3 : ℝ) / 2) * ((a - 1 : ℕ) : ℝ) ^ ((3 : ℝ) / 4) := by
  rw [retainedSize, Real.mul_rpow (Nat.cast_nonneg _) (sq_nonneg _),
    ← Real.rpow_natCast_mul (Nat.cast_nonneg _)]
  norm_num
  ring

theorem squaredEnvelope_endpoint (n : ℕ) (p : List ℕ) :
    squaredEnvelope n p ((3 : ℝ) / 4) =
      (n : ℝ) ^ (3 : ℕ) - partitionGain p * (n : ℝ) ^ ((3 : ℝ) / 2) := by
  have hbase : (n : ℝ) ^ ((9 : ℝ) / 4 + 3 / 4) = (n : ℝ) ^ (3 : ℕ) := by
    norm_num
  have hcor : ((n : ℝ) ^ 2) ^ ((3 : ℝ) / 4) = (n : ℝ) ^ ((3 : ℝ) / 2) := by
    rw [← Real.rpow_natCast_mul (Nat.cast_nonneg _)]
    norm_num
  induction p with
  | nil => simp [squaredEnvelope, partitionGain, hbase]
  | cons a p ih =>
    simp only [squaredEnvelope, List.length_cons, Nat.cast_add, Nat.cast_one,
      List.map_cons, List.sum_cons, hbase, hcor, retainedSize_endpoint] at ih ⊢
    simp only [partitionGain, List.map_cons, List.sum_cons, blockGain] at ih ⊢
    nlinarith

/-- All scalar work for NNN.1, separated from the tensor degeneration.
It suffices to establish the ordinary-block square envelope for every partition. -/
theorem linear_saving_of_partition_envelopes (n : ℕ) (hn : 7 ≤ n) (x : ℝ)
    (h : ∀ p : List ℕ, p.sum = n → (∀ a ∈ p, 7 ≤ a ∧ a ≤ 16) →
      ∃ u ∈ Set.Icc (0 : ℝ) (3 / 4), x ^ 2 ≤ squaredEnvelope n p u) :
    x ≤ (n : ℝ) ^ ((3 : ℝ) / 2) - (21 / 100 : ℝ) * n := by
  obtain ⟨p, hsum, hp, hgain⟩ := exists_partition_gain n hn
  obtain ⟨u, hu, hx⟩ := h p hsum hp
  have hm := squaredEnvelope_monotone n hn p hsum hp hu (by constructor <;> norm_num) hu.2
  have hs := hx.trans hm
  rw [squaredEnvelope_endpoint] at hs
  exact linear_saving_of_square_bound n hn x (partitionGain p) hgain hs

end OM.NNN
