import Lib.OM.NNN30.Partition.Count
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Growth of the partition numbers

`I = ∑_{m ≥ 1} 1/m²`, `Λ_K(s) = ∑_{k < K} -log(1 - e^{-s(k+1)})` (the logarithm of the truncated
product `∏_{k ≤ K} (1 - e^{-sk})⁻¹`), and `Z_N(s) = ∑_{n ≤ N} p(n) e^{-sn}`.

* `Lam_le`: `Λ_K(s) ≤ I/s` (expand `-log(1-y)`, swap the sums, `e^{-t}/(1 - e^{-t}) ≤ 1/t`);
  `Lam_eventually`: `Λ_K(s) ≥ (I - ε)/s` for small `s` and large `K` (`e^{-t}/(1-e^{-t}) ≥ 1/t - 1`).
* `Z_le`: `Z_N(s) ≤ e^{I/s}`; `Z_ge`: `Z_N(s) ≥ e^{(I - ε)/s}` for small `s` and some `N`
  (partitions against multiplicity vectors, `Lib/OM/NNN30/Partition/Count.lean`).
* `rankin`: both tails of `Z_N(s)` are controlled by `Z_N` at a smaller and a larger `s`.
* `log_Q_le`: `log Q(h) ≤ 2 √(I h)`; `log_Q_lower`: `log Q(h) ≥ (2 √I - η) √h` eventually
  (Rankin's trick on both tails at `s = √I (1+τ)/√h`, the lower tail cut at `h/(1+τ)⁴`).
* `tendsto_log_Q`, `tendsto_log_p`: `log Q(h)/√h → 2 √I` and `log p(h)/√h → 2 √I`
  (`p(h) ≤ Q(h) ≤ (h + 1) p(h)`).
-/

open Finset Real Filter Topology

namespace OM.NNN30.Partition

/-- `I = ∑_{m ≥ 1} 1/m²`. -/
noncomputable def Isum : ℝ := ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ 2

lemma summable_inv_sq : Summable (fun m : ℕ => 1 / ((m : ℝ) + 1) ^ 2) := by
  have h := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
  simpa [Nat.cast_add, Nat.cast_one] using h

lemma hasSum_Isum : HasSum (fun m : ℕ => 1 / ((m : ℝ) + 1) ^ 2) Isum := summable_inv_sq.hasSum

lemma Isum_pos : 0 < Isum := by
  have h := le_hasSum hasSum_Isum 0 (fun _ _ => by positivity)
  have h1 : (0 : ℝ) < 1 / (((0 : ℕ) : ℝ) + 1) ^ 2 := by norm_num
  linarith

/-- `Λ_K(s) = ∑_{k < K} -log(1 - e^{-s(k+1)})`. -/
noncomputable def Lam (K : ℕ) (s : ℝ) : ℝ :=
  ∑ k ∈ range K, -Real.log (1 - Real.exp (-(s * ((k : ℝ) + 1))))

lemma exp_neg_lt_one {t : ℝ} (ht : 0 < t) : Real.exp (-t) < 1 := by
  rw [Real.exp_lt_one_iff]; linarith

lemma hasSum_term {s : ℝ} (hs : 0 < s) (k : ℕ) :
    HasSum (fun m : ℕ => Real.exp (-(s * ((k : ℝ) + 1))) ^ (m + 1) / ((m : ℝ) + 1))
      (-Real.log (1 - Real.exp (-(s * ((k : ℝ) + 1))))) := by
  have h := Real.hasSum_pow_div_log_of_abs_lt_one
    (x := Real.exp (-(s * ((k : ℝ) + 1))))
    (by rw [abs_of_pos (Real.exp_pos _)]; exact exp_neg_lt_one (by positivity))
  simpa using h

lemma hasSum_Lam {s : ℝ} (hs : 0 < s) (K : ℕ) :
    HasSum (fun m : ℕ => ∑ k ∈ range K,
      Real.exp (-(s * ((k : ℝ) + 1))) ^ (m + 1) / ((m : ℝ) + 1)) (Lam K s) :=
  hasSum_sum (fun k _ => hasSum_term hs k)

/-- Rewriting the double sum: `e^{-s(k+1)(m+1)} = q_m^{k+1}` with `q_m = e^{-s(m+1)}`. -/
lemma term_swap (s : ℝ) (k m : ℕ) :
    Real.exp (-(s * ((k : ℝ) + 1))) ^ (m + 1) = Real.exp (-(s * ((m : ℝ) + 1))) ^ (k + 1) := by
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma geom_succ_eq {q : ℝ} (hq : q ≠ 1) (K : ℕ) :
    ∑ k ∈ range K, q ^ (k + 1) = q / (1 - q) * (1 - q ^ K) := by
  have h := geom_sum_eq hq K
  have h1 : ∑ k ∈ range K, q ^ (k + 1) = q * ∑ k ∈ range K, q ^ k := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [h1, h]
  have h2 : q - 1 ≠ 0 := sub_ne_zero.mpr hq
  have h3 : 1 - q ≠ 0 := fun h0 => hq (by linarith)
  field_simp
  ring

/-- `q/(1-q) ≤ 1/t` for `q = e^{-t}`, `t > 0`. -/
lemma ratio_le {t : ℝ} (ht : 0 < t) :
    Real.exp (-t) / (1 - Real.exp (-t)) ≤ 1 / t := by
  have hq1 := exp_neg_lt_one ht
  have hq0 := Real.exp_pos (-t)
  rw [div_le_div_iff₀ (by linarith) ht]
  have h := Real.add_one_le_exp t
  have he : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
  nlinarith

/-- `q/(1-q) ≥ 1/t - 1` for `q = e^{-t}`, `t > 0`. -/
lemma ratio_ge {t : ℝ} (ht : 0 < t) :
    1 / t - 1 ≤ Real.exp (-t) / (1 - Real.exp (-t)) := by
  have hq1 := exp_neg_lt_one ht
  have hq0 := Real.exp_pos (-t)
  have h := Real.add_one_le_exp (-t)
  rw [div_sub_one (ne_of_gt ht), div_le_div_iff₀ ht (by linarith)]
  nlinarith

/-- Upper bound: `Λ_K(s) ≤ I/s`. -/
lemma Lam_le {s : ℝ} (hs : 0 < s) (K : ℕ) : Lam K s ≤ Isum / s := by
  have hT : HasSum (fun m : ℕ => 1 / ((m : ℝ) + 1) ^ 2 / s) (Isum / s) := hasSum_Isum.div_const s
  refine hasSum_le (fun m => ?_) (hasSum_Lam hs K) hT
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have ht : 0 < s * ((m : ℝ) + 1) := by positivity
  have hq1 := exp_neg_lt_one ht
  have hq0 := Real.exp_pos (-(s * ((m : ℝ) + 1)))
  rw [← Finset.sum_div]
  simp_rw [term_swap s _ m]
  rw [geom_succ_eq (ne_of_lt hq1)]
  have hr := ratio_le ht
  have hpow : 0 ≤ Real.exp (-(s * ((m : ℝ) + 1))) ^ K := by positivity
  have hrat : 0 ≤ Real.exp (-(s * ((m : ℝ) + 1))) / (1 - Real.exp (-(s * ((m : ℝ) + 1)))) :=
    div_nonneg hq0.le (by linarith)
  have h1 : Real.exp (-(s * ((m : ℝ) + 1))) / (1 - Real.exp (-(s * ((m : ℝ) + 1)))) *
      (1 - Real.exp (-(s * ((m : ℝ) + 1))) ^ K) ≤ 1 / (s * ((m : ℝ) + 1)) := by
    calc _ ≤ Real.exp (-(s * ((m : ℝ) + 1))) / (1 - Real.exp (-(s * ((m : ℝ) + 1)))) * 1 :=
          mul_le_mul_of_nonneg_left (by linarith) hrat
      _ ≤ 1 / (s * ((m : ℝ) + 1)) := by rw [mul_one]; exact hr
  calc _ ≤ 1 / (s * ((m : ℝ) + 1)) / ((m : ℝ) + 1) := div_le_div_of_nonneg_right h1 hm.le
    _ = 1 / ((m : ℝ) + 1) ^ 2 / s := by field_simp

/-- Lower bound: `Λ_K(s) ≥ (1 - e^{-sK})/s · ∑_{m<M} 1/(m+1)² - ∑_{m<M} 1/(m+1)`. -/
lemma Lam_ge {s : ℝ} (hs : 0 < s) (K M : ℕ) :
    (1 - Real.exp (-(s * K))) / s * ∑ m ∈ range M, 1 / ((m : ℝ) + 1) ^ 2 -
      ∑ m ∈ range M, 1 / ((m : ℝ) + 1) ≤ Lam K s := by
  have hS := hasSum_Lam hs K
  have h1 := sum_le_hasSum (range M) (fun m _ => by
    apply Finset.sum_nonneg; intro k _; positivity) hS
  refine le_trans ?_ h1
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro m _
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have ht : 0 < s * ((m : ℝ) + 1) := by positivity
  have hq1 := exp_neg_lt_one ht
  have hq0 := Real.exp_pos (-(s * ((m : ℝ) + 1)))
  rw [← Finset.sum_div]
  simp_rw [term_swap s _ m]
  rw [geom_succ_eq (ne_of_lt hq1)]
  set q := Real.exp (-(s * ((m : ℝ) + 1))) with hq
  set β := 1 - Real.exp (-(s * K)) with hβ
  have hr := ratio_ge ht
  have hqK : q ^ K ≤ Real.exp (-(s * K)) := by
    rw [hq, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hK : (0 : ℝ) ≤ s * K * m := by positivity
    have e : (K : ℝ) * -(s * ((m : ℝ) + 1)) = -(s * K) - s * K * m := by ring
    rw [e]; linarith
  have hqK0 : 0 ≤ q ^ K := by positivity
  have hqK1 : q ^ K ≤ 1 := pow_le_one₀ hq0.le hq1.le
  -- (q/(1-q))(1 - q^K) ≥ β/(s(m+1)) - 1
  have hc : 0 < 1 / (s * ((m : ℝ) + 1)) := by positivity
  have key : β / (s * ((m : ℝ) + 1)) - 1 ≤ q / (1 - q) * (1 - q ^ K) := by
    have e1 : β / (s * ((m : ℝ) + 1)) = β * (1 / (s * ((m : ℝ) + 1))) := by ring
    rw [e1]
    have hb : β ≤ 1 - q ^ K := by rw [hβ]; linarith
    nlinarith [mul_le_mul_of_nonneg_right hb hc.le, mul_le_mul_of_nonneg_right hr (by linarith : (0:ℝ) ≤ 1 - q ^ K)]
  calc β / s * (1 / ((m : ℝ) + 1) ^ 2) - 1 / ((m : ℝ) + 1)
      = (β / (s * ((m : ℝ) + 1)) - 1) / ((m : ℝ) + 1) := by field_simp
    _ ≤ q / (1 - q) * (1 - q ^ K) / ((m : ℝ) + 1) := div_le_div_of_nonneg_right key hm.le

/-- For every `ε > 0` and all small `s`, some `Λ_K(s)` is at least `(I - ε)/s`. -/
lemma Lam_eventually {ε : ℝ} (hε : 0 < ε) :
    ∃ s0 : ℝ, 0 < s0 ∧ ∀ s : ℝ, 0 < s → s ≤ s0 → ∃ K : ℕ, (Isum - ε) / s ≤ Lam K s := by
  have hT := hasSum_Isum.tendsto_sum_nat
  obtain ⟨M, hM⟩ : ∃ M : ℕ, Isum - ε / 4 < ∑ m ∈ range M, 1 / ((m : ℝ) + 1) ^ 2 :=
    (hT.eventually (Ioi_mem_nhds (show Isum - ε / 4 < Isum by linarith))).exists
  set S2 := ∑ m ∈ range M, 1 / ((m : ℝ) + 1) ^ 2 with hS2
  set H := ∑ m ∈ range M, 1 / ((m : ℝ) + 1) with hH
  have hS2le : S2 ≤ Isum := sum_le_hasSum (range M) (fun _ _ => by positivity) hasSum_Isum
  have hH0 : 0 ≤ H := Finset.sum_nonneg (fun _ _ => by positivity)
  have hS20 : 0 ≤ S2 := Finset.sum_nonneg (fun _ _ => by positivity)
  have hI0 := Isum_pos
  refine ⟨ε / (4 * (H + 1)), by positivity, ?_⟩
  intro s hs hss0
  have hx : Real.exp (-s) < 1 := exp_neg_lt_one hs
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos (-s)).le hx
  obtain ⟨K, hK⟩ := (hlim.eventually (Iio_mem_nhds (show (0 : ℝ) < ε / (4 * (Isum + 1)) by
    positivity))).exists
  refine ⟨K, ?_⟩
  have hLam := Lam_ge hs K M
  have heK : Real.exp (-s) ^ K = Real.exp (-(s * K)) := by
    rw [← Real.exp_nat_mul]; ring_nf
  rw [heK] at hK
  set e := Real.exp (-(s * K)) with he
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have h1 : e * S2 ≤ e * Isum := mul_le_mul_of_nonneg_left hS2le he0
  have h2 : e * Isum ≤ ε / 4 := by
    have h2a : e * Isum ≤ ε / (4 * (Isum + 1)) * Isum := mul_le_mul_of_nonneg_right hK.le hI0.le
    have h2b : ε / (4 * (Isum + 1)) * Isum ≤ ε / 4 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have h3 : H * s ≤ ε / 4 := by
    have h3a : H * s ≤ H * (ε / (4 * (H + 1))) := mul_le_mul_of_nonneg_left hss0 hH0
    have h3b : H * (ε / (4 * (H + 1))) ≤ ε / 4 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have key : Isum - ε ≤ (1 - e) * S2 - H * s := by nlinarith
  calc (Isum - ε) / s ≤ ((1 - e) * S2 - H * s) / s := div_le_div_of_nonneg_right key hs.le
    _ = (1 - e) / s * S2 - H := by field_simp
    _ ≤ Lam K s := hLam

/-! ## The truncated generating function `Z_N(s) = ∑_{n ≤ N} p(n) e^{-sn}` -/

/-- `Z_N(s) = ∑_{n ≤ N} p(n) e^{-sn}`. -/
noncomputable def Z (N : ℕ) (s : ℝ) : ℝ := ∑ n ∈ range (N + 1), (pn n : ℝ) * Real.exp (-(s * n))

lemma Z_eq (N : ℕ) (s : ℝ) : Z N s = ∑ n ∈ range (N + 1), (pn n : ℝ) * Real.exp (-s) ^ n := by
  unfold Z
  apply Finset.sum_congr rfl
  intro n _
  rw [← Real.exp_nat_mul]; ring_nf

lemma Z_mono (s : ℝ) {N N' : ℕ} (h : N ≤ N') : Z N s ≤ Z N' s := by
  unfold Z
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
  intro n _ _; positivity

lemma prod_eq_exp_Lam {s : ℝ} (hs : 0 < s) (K : ℕ) :
    ∏ k : Fin K, 1 / (1 - Real.exp (-s) ^ ((k : ℕ) + 1)) = Real.exp (Lam K s) := by
  unfold Lam
  rw [Real.exp_sum, Fin.prod_univ_eq_prod_range (fun k => 1 / (1 - Real.exp (-s) ^ (k + 1)))]
  apply Finset.prod_congr rfl
  intro k _
  have hy : Real.exp (-s) ^ (k + 1) = Real.exp (-(s * ((k : ℝ) + 1))) := by
    rw [← Real.exp_nat_mul]; push_cast; ring_nf
  have hpos : 0 < 1 - Real.exp (-(s * ((k : ℝ) + 1))) := by
    have := exp_neg_lt_one (show 0 < s * ((k : ℝ) + 1) by positivity); linarith
  rw [hy, one_div, Real.exp_neg (Real.log (1 - Real.exp (-(s * ((k : ℝ) + 1))))),
    Real.exp_log hpos]

lemma geom_fin_le {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) (C : ℕ) :
    ∑ c ∈ range (C + 1), y ^ c ≤ 1 / (1 - y) := by
  have := geom_sum_Ico_le_of_lt_one (m := 0) (n := C + 1) hy0 hy1
  rwa [← Finset.range_eq_Ico, pow_zero] at this

lemma geom_fin_ge {x y : ℝ} (hy0 : 0 ≤ y) (hyx : y ≤ x) (hx1 : x < 1) (C : ℕ) :
    (1 - x ^ (C + 1)) / (1 - y) ≤ ∑ c ∈ range (C + 1), y ^ c := by
  have hy1 : y < 1 := lt_of_le_of_lt hyx hx1
  rw [geom_sum_eq (ne_of_lt hy1)]
  have h1 : (y ^ (C + 1) - 1) / (y - 1) = (1 - y ^ (C + 1)) / (1 - y) := by
    have hne1 : y - 1 ≠ 0 := ne_of_lt (by linarith)
    have hne2 : 1 - y ≠ 0 := ne_of_gt (by linarith)
    rw [div_eq_div_iff hne1 hne2]; ring
  rw [h1]
  apply div_le_div_of_nonneg_right _ (by linarith)
  have : y ^ (C + 1) ≤ x ^ (C + 1) := pow_le_pow_left₀ hy0 hyx _
  linarith

/-- `Z_N(s) ≤ e^{I/s}`. -/
lemma Z_le {s : ℝ} (hs : 0 < s) (N : ℕ) : Z N s ≤ Real.exp (Isum / s) := by
  rw [Z_eq]
  have hx0 : 0 ≤ Real.exp (-s) := (Real.exp_pos _).le
  have hx1 : Real.exp (-s) < 1 := exp_neg_lt_one hs
  refine (sum_pn_le_prod hx0 N).trans ?_
  calc ∏ k : Fin N, ∑ c : Fin (N + 1), Real.exp (-s) ^ (((k : ℕ) + 1) * (c : ℕ))
      ≤ ∏ k : Fin N, 1 / (1 - Real.exp (-s) ^ ((k : ℕ) + 1)) := by
        apply Finset.prod_le_prod₀
        · intro k _; exact Finset.sum_nonneg (fun c _ => pow_nonneg hx0 _)
        · intro k _
          have hy0 : 0 ≤ Real.exp (-s) ^ ((k : ℕ) + 1) := pow_nonneg hx0 _
          have hy1 : Real.exp (-s) ^ ((k : ℕ) + 1) < 1 := pow_lt_one₀ hx0 hx1 (by omega)
          rw [Fin.sum_univ_eq_sum_range (fun c => Real.exp (-s) ^ (((k : ℕ) + 1) * c))]
          simp_rw [pow_mul]
          exact geom_fin_le hy0 hy1 N
    _ = Real.exp (Lam N s) := prod_eq_exp_Lam hs N
    _ ≤ Real.exp (Isum / s) := Real.exp_le_exp.mpr (Lam_le hs N)

/-- For every `ε > 0` and all small `s`, some `Z_N(s)` is at least `e^{(I - ε)/s}`. -/
lemma Z_ge {ε : ℝ} (hε : 0 < ε) :
    ∃ s0 : ℝ, 0 < s0 ∧ ∀ s : ℝ, 0 < s → s ≤ s0 → ∃ N : ℕ,
      Real.exp ((Isum - ε) / s) ≤ Z N s := by
  obtain ⟨s1, hs1, h1⟩ := Lam_eventually (half_pos hε)
  refine ⟨min s1 (ε / 2), lt_min hs1 (half_pos hε), ?_⟩
  intro s hs hss
  obtain ⟨K, hK⟩ := h1 s hs (hss.trans (min_le_left _ _))
  have hx0 : 0 ≤ Real.exp (-s) := (Real.exp_pos _).le
  have hx1 : Real.exp (-s) < 1 := exp_neg_lt_one hs
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one hx0 hx1
  obtain ⟨C, hC⟩ := (hlim.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 / (2 * ((K : ℝ) + 1)) by
    positivity))).exists
  have hC1 : Real.exp (-s) ^ (C + 1) ≤ Real.exp (-s) ^ C :=
    pow_le_pow_of_le_one hx0 hx1.le (by omega)
  have hKC : (K : ℝ) * Real.exp (-s) ^ (C + 1) ≤ 1 / 2 := by
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    have h2 : (K : ℝ) * Real.exp (-s) ^ (C + 1) ≤ (K : ℝ) * (1 / (2 * ((K : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_left (hC1.trans hC.le) hK0
    have h3 : (K : ℝ) * (1 / (2 * ((K : ℝ) + 1))) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  refine ⟨K * K * C, ?_⟩
  rw [Z_eq]
  refine le_trans ?_ (prod_le_sum_pn hx0 K C)
  set x := Real.exp (-s) with hx
  have hfac : ∀ k : Fin K, (1 - x ^ (C + 1)) * (1 / (1 - x ^ ((k : ℕ) + 1))) ≤
      ∑ c : Fin (C + 1), x ^ (((k : ℕ) + 1) * (c : ℕ)) := by
    intro k
    have hy0 : 0 ≤ x ^ ((k : ℕ) + 1) := pow_nonneg hx0 _
    have hyx : x ^ ((k : ℕ) + 1) ≤ x := by
      calc x ^ ((k : ℕ) + 1) ≤ x ^ 1 := pow_le_pow_of_le_one hx0 hx1.le (by omega)
        _ = x := pow_one x
    rw [Fin.sum_univ_eq_sum_range (fun c => x ^ (((k : ℕ) + 1) * c))]
    simp_rw [pow_mul]
    have := geom_fin_ge hy0 hyx hx1 C
    rw [mul_one_div]; exact this
  have hprod : (1 - x ^ (C + 1)) ^ K * Real.exp (Lam K s) ≤
      ∏ k : Fin K, ∑ c : Fin (C + 1), x ^ (((k : ℕ) + 1) * (c : ℕ)) := by
    rw [← prod_eq_exp_Lam hs K]
    have e1 : (1 - x ^ (C + 1)) ^ K = ∏ _k : Fin K, (1 - x ^ (C + 1)) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [e1, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod₀
    · intro k _
      have hxC : x ^ (C + 1) < 1 := pow_lt_one₀ hx0 hx1 (by omega)
      have hy1 : x ^ ((k : ℕ) + 1) < 1 := pow_lt_one₀ hx0 hx1 (by omega)
      have : 0 < 1 / (1 - x ^ ((k : ℕ) + 1)) := by
        apply div_pos one_pos; linarith
      exact mul_nonneg (by linarith) this.le
    · intro k _; exact hfac k
  have hbern : 1 / 2 ≤ (1 - x ^ (C + 1)) ^ K := by
    have h := one_add_mul_le_pow (a := -x ^ (C + 1))
      (by have := pow_le_one₀ hx0 hx1.le (n := C + 1); linarith) K
    have e2 : (1 : ℝ) + -x ^ (C + 1) = 1 - x ^ (C + 1) := by ring
    rw [e2] at h
    linarith
  have hexp : Real.exp ((Isum - ε) / s) * 2 ≤ Real.exp (Lam K s) := by
    have hss2 : s ≤ ε / 2 := hss.trans (min_le_right _ _)
    have h1' : (Isum - ε) / s + ε / 2 / s ≤ Lam K s := by
      have : (Isum - ε) / s + ε / 2 / s = (Isum - ε / 2) / s := by field_simp; ring
      rw [this]; exact hK
    have h2 : (2 : ℝ) ≤ Real.exp (ε / 2 / s) := by
      have h3 : (1 : ℝ) ≤ ε / 2 / s := by rw [le_div_iff₀ hs]; linarith
      have h4 := Real.add_one_le_exp (ε / 2 / s)
      linarith
    calc Real.exp ((Isum - ε) / s) * 2 ≤ Real.exp ((Isum - ε) / s) * Real.exp (ε / 2 / s) :=
          mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
      _ = Real.exp ((Isum - ε) / s + ε / 2 / s) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (Lam K s) := Real.exp_le_exp.mpr h1'
  have hE := (Real.exp_pos (Lam K s)).le
  calc Real.exp ((Isum - ε) / s) ≤ 1 / 2 * Real.exp (Lam K s) := by linarith
    _ ≤ (1 - x ^ (C + 1)) ^ K * Real.exp (Lam K s) := mul_le_mul_of_nonneg_right hbern hE
    _ ≤ _ := hprod

/-! ## Rankin's trick on both tails -/

/-- `Q(h) = ∑_{j ≤ h} p(j)`, as a real number. -/
noncomputable def Qr (h : ℕ) : ℝ := ∑ j ∈ range (h + 1), (pn j : ℝ)

lemma rankin {s s' s'' A : ℝ} {h N : ℕ} (hs' : 0 ≤ s') (hss' : s' ≤ s) (hss'' : s ≤ s'') :
    Z N s ≤ Real.exp ((s'' - s) * A) * Z N s'' + Real.exp (-(s * A)) * Qr h +
      Real.exp (-((s - s') * h)) * Z N s' := by
  unfold Z
  rw [← Finset.sum_filter_add_sum_filter_not (range (N + 1)) (fun n : ℕ => (n : ℝ) < A)]
  rw [← Finset.sum_filter_add_sum_filter_not
    ((range (N + 1)).filter (fun n : ℕ => ¬ (n : ℝ) < A)) (fun n : ℕ => n ≤ h)]
  rw [Finset.filter_filter, Finset.filter_filter]
  have hs0 : 0 ≤ s := hs'.trans hss'
  -- lower tail
  have hP1 : ∑ n ∈ (range (N + 1)).filter (fun n : ℕ => (n : ℝ) < A),
      (pn n : ℝ) * Real.exp (-(s * n)) ≤
      Real.exp ((s'' - s) * A) * ∑ n ∈ range (N + 1), (pn n : ℝ) * Real.exp (-(s'' * n)) := by
    rw [Finset.mul_sum]
    calc _ ≤ ∑ n ∈ (range (N + 1)).filter (fun n : ℕ => (n : ℝ) < A),
          Real.exp ((s'' - s) * A) * ((pn n : ℝ) * Real.exp (-(s'' * n))) := by
          apply Finset.sum_le_sum
          intro n hn
          have hnA : (n : ℝ) < A := (Finset.mem_filter.mp hn).2
          have he : Real.exp (-(s * n)) ≤ Real.exp ((s'' - s) * A) * Real.exp (-(s'' * n)) := by
            rw [← Real.exp_add]
            apply Real.exp_le_exp.mpr
            nlinarith
          calc (pn n : ℝ) * Real.exp (-(s * n))
              ≤ (pn n : ℝ) * (Real.exp ((s'' - s) * A) * Real.exp (-(s'' * n))) :=
                mul_le_mul_of_nonneg_left he (Nat.cast_nonneg _)
            _ = _ := by ring
      _ ≤ _ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro n _ _; positivity
  -- middle
  have hP2 : ∑ n ∈ (range (N + 1)).filter (fun n : ℕ => ¬ (n : ℝ) < A ∧ n ≤ h),
      (pn n : ℝ) * Real.exp (-(s * n)) ≤ Real.exp (-(s * A)) * Qr h := by
    unfold Qr
    rw [Finset.mul_sum]
    calc _ ≤ ∑ n ∈ (range (N + 1)).filter (fun n : ℕ => ¬ (n : ℝ) < A ∧ n ≤ h),
          Real.exp (-(s * A)) * (pn n : ℝ) := by
          apply Finset.sum_le_sum
          intro n hn
          have hnA : ¬ (n : ℝ) < A := (Finset.mem_filter.mp hn).2.1
          have he : Real.exp (-(s * n)) ≤ Real.exp (-(s * A)) := by
            apply Real.exp_le_exp.mpr
            have : A ≤ (n : ℝ) := le_of_not_gt hnA
            nlinarith
          calc (pn n : ℝ) * Real.exp (-(s * n)) ≤ (pn n : ℝ) * Real.exp (-(s * A)) :=
                mul_le_mul_of_nonneg_left he (Nat.cast_nonneg _)
            _ = _ := by ring
      _ ≤ _ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro n hn
            have := (Finset.mem_filter.mp hn).2.2
            exact Finset.mem_range.mpr (Nat.lt_succ_of_le this)
          · intro n _ _; positivity
  -- upper tail
  have hP3 : ∑ n ∈ (range (N + 1)).filter (fun n : ℕ => ¬ (n : ℝ) < A ∧ ¬ n ≤ h),
      (pn n : ℝ) * Real.exp (-(s * n)) ≤
      Real.exp (-((s - s') * h)) * ∑ n ∈ range (N + 1), (pn n : ℝ) * Real.exp (-(s' * n)) := by
    rw [Finset.mul_sum]
    calc _ ≤ ∑ n ∈ (range (N + 1)).filter (fun n : ℕ => ¬ (n : ℝ) < A ∧ ¬ n ≤ h),
          Real.exp (-((s - s') * h)) * ((pn n : ℝ) * Real.exp (-(s' * n))) := by
          apply Finset.sum_le_sum
          intro n hn
          have hnh : ¬ n ≤ h := (Finset.mem_filter.mp hn).2.2
          have hnh' : (h : ℝ) ≤ n := by exact_mod_cast (le_of_lt (not_le.mp hnh))
          have he : Real.exp (-(s * n)) ≤ Real.exp (-((s - s') * h)) * Real.exp (-(s' * n)) := by
            rw [← Real.exp_add]
            apply Real.exp_le_exp.mpr
            nlinarith
          calc (pn n : ℝ) * Real.exp (-(s * n))
              ≤ (pn n : ℝ) * (Real.exp (-((s - s') * h)) * Real.exp (-(s' * n))) :=
                mul_le_mul_of_nonneg_left he (Nat.cast_nonneg _)
            _ = _ := by ring
      _ ≤ _ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro n _ _; positivity
  linarith


lemma rhs_eq (r τ : ℝ) (hr : 0 < r) (hτ : 0 ≤ τ) :
    (r ^ 2 - r ^ 2 * τ ^ 2 / (2 * (1 + τ) ^ 2)) / (r * (1 + τ)) - r * τ ^ 2 / (2 * (1 + τ) ^ 3) =
      r * (1 + 2 * τ) / (1 + τ) ^ 3 := by
  have h1 : (0 : ℝ) < 1 + τ := by linarith
  field_simp
  ring

lemma alg_U (r τ : ℝ) (hr : 0 < r) (hτ : 0 ≤ τ) :
    -(r * (1 + τ) - r) + r ^ 2 / r ≤
      (r ^ 2 - r ^ 2 * τ ^ 2 / (2 * (1 + τ) ^ 2)) / (r * (1 + τ)) - r * τ ^ 2 / (2 * (1 + τ) ^ 3) := by
  rw [rhs_eq r τ hr hτ]
  have h1 : (0 : ℝ) < 1 + τ := by linarith
  have e : -(r * (1 + τ) - r) + r ^ 2 / r = r * (1 - τ) := by field_simp; ring
  rw [e, le_div_iff₀ (by positivity)]
  have h2 : (1 - τ) * (1 + τ) ^ 3 ≤ 1 + 2 * τ := by nlinarith [pow_nonneg hτ 3, pow_nonneg hτ 4]
  nlinarith [mul_le_mul_of_nonneg_left h2 hr.le]

lemma alg_L (r τ : ℝ) (hr : 0 < r) (hτ : 0 ≤ τ) :
    (r * (1 + τ) ^ 2 - r * (1 + τ)) * (1 / (1 + τ) ^ 4) + r ^ 2 / (r * (1 + τ) ^ 2) ≤
      (r ^ 2 - r ^ 2 * τ ^ 2 / (2 * (1 + τ) ^ 2)) / (r * (1 + τ)) - r * τ ^ 2 / (2 * (1 + τ) ^ 3) := by
  rw [rhs_eq r τ hr hτ]
  have h1 : (0 : ℝ) < 1 + τ := by linarith
  apply le_of_eq
  field_simp
  ring

lemma alg_B (r τ : ℝ) (hr : 0 < r) (hτ : 0 ≤ τ) :
    r * (2 - 5 * τ) ≤ r * (1 + τ) * (1 / (1 + τ) ^ 4) +
      (r ^ 2 - r ^ 2 * τ ^ 2 / (2 * (1 + τ) ^ 2)) / (r * (1 + τ)) := by
  have h1 : (0 : ℝ) < 1 + τ := by linarith
  have e : r * (1 + τ) * (1 / (1 + τ) ^ 4) +
      (r ^ 2 - r ^ 2 * τ ^ 2 / (2 * (1 + τ) ^ 2)) / (r * (1 + τ)) =
      r * (2 + 2 * τ + τ ^ 2 / 2) / (1 + τ) ^ 3 := by field_simp; ring
  rw [e, le_div_iff₀ (by positivity)]
  have h2 : (2 - 5 * τ) * (1 + τ) ^ 3 ≤ 2 + 2 * τ + τ ^ 2 / 2 := by
    nlinarith [pow_nonneg hτ 2, pow_nonneg hτ 3, pow_nonneg hτ 4]
  nlinarith [mul_le_mul_of_nonneg_left h2 hr.le]

/-! ## The two-tail estimate in logarithmic form -/

lemma log_Q_ge {t c c' c'' a ε κ : ℝ} {h N : ℕ} (ht : 0 < t) (hh : (h : ℝ) = t ^ 2)
    (hc' : 0 < c') (hcc' : c' ≤ c) (hcc'' : c ≤ c'')
    (hU : -(c - c') + Isum / c' ≤ (Isum - ε) / c - κ)
    (hL : (c'' - c) * a + Isum / c'' ≤ (Isum - ε) / c - κ)
    (hκ : Real.log 4 ≤ t * κ)
    (hZ : Real.exp ((Isum - ε) / (c / t)) ≤ Z N (c / t)) :
    t * (c * a + (Isum - ε) / c) - Real.log 2 ≤ Real.log (Qr h) := by
  have hc : 0 < c := lt_of_lt_of_le hc' hcc'
  have hc'' : 0 < c'' := lt_of_lt_of_le hc hcc''
  have hs : 0 < c / t := div_pos hc ht
  have hs' : 0 < c' / t := div_pos hc' ht
  have hs'' : 0 < c'' / t := div_pos hc'' ht
  have hss' : c' / t ≤ c / t := div_le_div_of_nonneg_right hcc' ht.le
  have hss'' : c / t ≤ c'' / t := div_le_div_of_nonneg_right hcc'' ht.le
  have hR := rankin (A := a * (h : ℝ)) (h := h) (N := N) hs'.le hss' hss''
  have hZ'' := Z_le hs'' N
  have hZ' := Z_le hs' N
  have e2 : (Isum - ε) / (c / t) = t * ((Isum - ε) / c) := by field_simp
  have hX1 : (c'' / t - c / t) * (a * (h : ℝ)) + Isum / (c'' / t) ≤
      (Isum - ε) / (c / t) - Real.log 4 := by
    have e1 : (c'' / t - c / t) * (a * (h : ℝ)) + Isum / (c'' / t) =
        t * ((c'' - c) * a + Isum / c'') := by rw [hh]; field_simp
    rw [e1, e2]
    nlinarith [mul_le_mul_of_nonneg_left hL ht.le]
  have hX2 : -((c / t - c' / t) * (h : ℝ)) + Isum / (c' / t) ≤
      (Isum - ε) / (c / t) - Real.log 4 := by
    have e1 : -((c / t - c' / t) * (h : ℝ)) + Isum / (c' / t) = t * (-(c - c') + Isum / c') := by
      rw [hh]; field_simp
    rw [e1, e2]
    nlinarith [mul_le_mul_of_nonneg_left hU ht.le]
  have h4 : Real.exp (Real.log 4) = 4 := Real.exp_log (by norm_num)
  have hT1 : Real.exp ((c'' / t - c / t) * (a * (h : ℝ))) * Z N (c'' / t) ≤
      Real.exp ((Isum - ε) / (c / t)) / 4 := by
    calc Real.exp ((c'' / t - c / t) * (a * (h : ℝ))) * Z N (c'' / t)
        ≤ Real.exp ((c'' / t - c / t) * (a * (h : ℝ))) * Real.exp (Isum / (c'' / t)) :=
          mul_le_mul_of_nonneg_left hZ'' (Real.exp_pos _).le
      _ = Real.exp ((c'' / t - c / t) * (a * (h : ℝ)) + Isum / (c'' / t)) :=
          (Real.exp_add _ _).symm
      _ ≤ Real.exp ((Isum - ε) / (c / t) - Real.log 4) := Real.exp_le_exp.mpr hX1
      _ = Real.exp ((Isum - ε) / (c / t)) / 4 := by rw [Real.exp_sub, h4]
  have hT2 : Real.exp (-((c / t - c' / t) * (h : ℝ))) * Z N (c' / t) ≤
      Real.exp ((Isum - ε) / (c / t)) / 4 := by
    calc Real.exp (-((c / t - c' / t) * (h : ℝ))) * Z N (c' / t)
        ≤ Real.exp (-((c / t - c' / t) * (h : ℝ))) * Real.exp (Isum / (c' / t)) :=
          mul_le_mul_of_nonneg_left hZ' (Real.exp_pos _).le
      _ = Real.exp (-((c / t - c' / t) * (h : ℝ)) + Isum / (c' / t)) := (Real.exp_add _ _).symm
      _ ≤ Real.exp ((Isum - ε) / (c / t) - Real.log 4) := Real.exp_le_exp.mpr hX2
      _ = Real.exp ((Isum - ε) / (c / t)) / 4 := by rw [Real.exp_sub, h4]
  have hQ : Real.exp ((Isum - ε) / (c / t)) / 2 ≤ Real.exp (-(c / t * (a * (h : ℝ)))) * Qr h := by
    linarith
  have hEA : Real.exp ((Isum - ε) / (c / t) + c / t * (a * (h : ℝ))) / 2 ≤ Qr h := by
    have hpos := Real.exp_pos (c / t * (a * (h : ℝ)))
    have e3 : Real.exp (-(c / t * (a * (h : ℝ)))) * Real.exp (c / t * (a * (h : ℝ))) = 1 := by
      rw [← Real.exp_add]; simp
    calc Real.exp ((Isum - ε) / (c / t) + c / t * (a * (h : ℝ))) / 2
        = Real.exp ((Isum - ε) / (c / t)) / 2 * Real.exp (c / t * (a * (h : ℝ))) := by
          rw [Real.exp_add]; ring
      _ ≤ Real.exp (-(c / t * (a * (h : ℝ)))) * Qr h * Real.exp (c / t * (a * (h : ℝ))) :=
          mul_le_mul_of_nonneg_right hQ hpos.le
      _ = Qr h := by rw [mul_comm (Real.exp _) (Qr h), mul_assoc, e3, mul_one]
  have hlog := Real.log_le_log (by positivity) hEA
  rw [Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp] at hlog
  have e4 : (Isum - ε) / (c / t) + c / t * (a * (h : ℝ)) = t * (c * a + (Isum - ε) / c) := by
    rw [hh]; field_simp; ring
  rw [e4] at hlog
  exact hlog

/-- Upper bound: `log Q(h) ≤ 2 √I √h`. -/
lemma log_Q_le {h : ℕ} (hh : 1 ≤ h) : Real.log (Qr h) ≤ 2 * Real.sqrt Isum * Real.sqrt h := by
  set r := Real.sqrt Isum with hr_def
  have hr : 0 < r := Real.sqrt_pos.mpr Isum_pos
  have hr2 : r ^ 2 = Isum := Real.sq_sqrt Isum_pos.le
  set t := Real.sqrt h with ht_def
  have ht : 0 < t := Real.sqrt_pos.mpr (by exact_mod_cast hh)
  have hht : (h : ℝ) = t ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg h)).symm
  have hs : 0 < r / t := div_pos hr ht
  have hQZ : Qr h ≤ Real.exp (r / t * h) * Z h (r / t) := by
    unfold Qr Z
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    have hnh : (n : ℝ) ≤ h := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    have he : 1 ≤ Real.exp (r / t * h) * Real.exp (-(r / t * n)) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      nlinarith
    calc (pn n : ℝ) = (pn n : ℝ) * 1 := by ring
      _ ≤ (pn n : ℝ) * (Real.exp (r / t * h) * Real.exp (-(r / t * n))) :=
          mul_le_mul_of_nonneg_left he (Nat.cast_nonneg _)
      _ = _ := by ring
  have hZ := Z_le hs h
  have hQpos : 0 < Qr h := by
    unfold Qr
    exact Finset.sum_pos (fun j _ => by exact_mod_cast one_le_pn j) ⟨0, by simp⟩
  have h2 : Qr h ≤ Real.exp (r / t * h + Isum / (r / t)) := by
    calc Qr h ≤ Real.exp (r / t * h) * Z h (r / t) := hQZ
      _ ≤ Real.exp (r / t * h) * Real.exp (Isum / (r / t)) :=
          mul_le_mul_of_nonneg_left hZ (Real.exp_pos _).le
      _ = _ := (Real.exp_add _ _).symm
  have e : r / t * h + Isum / (r / t) = 2 * r * t := by
    rw [hht, ← hr2]; field_simp; ring
  rw [e] at h2
  calc Real.log (Qr h) ≤ Real.log (Real.exp (2 * r * t)) := Real.log_le_log hQpos h2
    _ = 2 * r * t := Real.log_exp _

/-- Lower bound: for every `η > 0`, eventually `log Q(h) ≥ (2 √I - η) √h`. -/
lemma log_Q_lower {η : ℝ} (hη : 0 < η) :
    ∀ᶠ h : ℕ in atTop, (2 * Real.sqrt Isum - η) * Real.sqrt h ≤ Real.log (Qr h) := by
  set r := Real.sqrt Isum with hr_def
  have hr : 0 < r := Real.sqrt_pos.mpr Isum_pos
  have hr2 : r ^ 2 = Isum := Real.sq_sqrt Isum_pos.le
  set τ := min 1 (η / (10 * r)) with hτ_def
  have hτ0 : 0 < τ := lt_min one_pos (by positivity)
  have hτη : τ ≤ η / (10 * r) := min_le_right _ _
  have hγ0 : (0 : ℝ) < 1 + τ := by linarith
  set ε := r ^ 2 * τ ^ 2 / (2 * (1 + τ) ^ 2) with hε_def
  set κ := r * τ ^ 2 / (2 * (1 + τ) ^ 3) with hκ_def
  have hε : 0 < ε := by positivity
  have hκ : 0 < κ := by positivity
  obtain ⟨s0, hs0, hZs⟩ := Z_ge hε
  set T0 := max (max (r * (1 + τ) / s0) (Real.log 4 / κ)) (2 * Real.log 2 / η) with hT0_def
  have hT0a : r * (1 + τ) / s0 ≤ T0 := le_trans (le_max_left _ _) (le_max_left _ _)
  have hT0b : Real.log 4 / κ ≤ T0 := le_trans (le_max_right _ _) (le_max_left _ _)
  have hT0c : 2 * Real.log 2 / η ≤ T0 := le_max_right _ _
  have hT0 : 0 < T0 := lt_of_lt_of_le (by positivity) hT0a
  have hsqrt : Tendsto (fun h : ℕ => Real.sqrt h) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hsqrt.eventually_ge_atTop T0] with h hh
  set t := Real.sqrt h with ht_def
  have ht : 0 < t := lt_of_lt_of_le hT0 hh
  have hht : (h : ℝ) = t ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg h)).symm
  have hs_le : r * (1 + τ) / t ≤ s0 := by
    have h1 : r * (1 + τ) / s0 ≤ t := hT0a.trans hh
    rw [div_le_iff₀ hs0] at h1
    rw [div_le_iff₀ ht]; linarith
  obtain ⟨N0, hN0⟩ := hZs (r * (1 + τ) / t) (by positivity) hs_le
  have hZ : Real.exp ((Isum - ε) / (r * (1 + τ) / t)) ≤ Z (max N0 h) (r * (1 + τ) / t) :=
    hN0.trans (Z_mono _ (le_max_left _ _))
  have hκt : Real.log 4 ≤ t * κ := by
    have h1 : Real.log 4 / κ ≤ t := hT0b.trans hh
    rw [div_le_iff₀ hκ] at h1; linarith
  have hU : -(r * (1 + τ) - r) + Isum / r ≤ (Isum - ε) / (r * (1 + τ)) - κ := by
    rw [← hr2]; exact alg_U r τ hr hτ0.le
  have hL : (r * (1 + τ) ^ 2 - r * (1 + τ)) * (1 / (1 + τ) ^ 4) + Isum / (r * (1 + τ) ^ 2) ≤
      (Isum - ε) / (r * (1 + τ)) - κ := by
    rw [← hr2]; exact alg_L r τ hr hτ0.le
  have hcc' : r ≤ r * (1 + τ) := by nlinarith
  have hcc'' : r * (1 + τ) ≤ r * (1 + τ) ^ 2 := by nlinarith
  have hmain := log_Q_ge (a := 1 / (1 + τ) ^ 4) ht hht hr hcc' hcc'' hU hL hκt hZ
  have hbr : r * (2 - 5 * τ) ≤ r * (1 + τ) * (1 / (1 + τ) ^ 4) + (Isum - ε) / (r * (1 + τ)) := by
    rw [← hr2]; exact alg_B r τ hr hτ0.le
  have h5 : 5 * r * τ ≤ η / 2 := by
    have := mul_le_mul_of_nonneg_left hτη (by positivity : (0 : ℝ) ≤ 5 * r)
    have e : 5 * r * (η / (10 * r)) = η / 2 := by field_simp; ring
    linarith
  have hlog2 : Real.log 2 ≤ t * (η / 2) := by
    have h1 : 2 * Real.log 2 / η ≤ t := hT0c.trans hh
    rw [div_le_iff₀ hη] at h1; linarith
  nlinarith [mul_le_mul_of_nonneg_left hbr ht.le]

/-! ## The limits -/

lemma tendsto_log_Q :
    Tendsto (fun h : ℕ => Real.log (Qr h) / Real.sqrt h) atTop (𝓝 (2 * Real.sqrt Isum)) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    have hη : 0 < (2 * Real.sqrt Isum - a) / 2 := by linarith
    filter_upwards [log_Q_lower hη, eventually_ge_atTop 1] with h hh h1
    have ht : 0 < Real.sqrt h := Real.sqrt_pos.mpr (by exact_mod_cast h1)
    rw [lt_div_iff₀ ht]
    nlinarith
  · intro a ha
    filter_upwards [eventually_ge_atTop 1] with h h1
    have ht : 0 < Real.sqrt h := Real.sqrt_pos.mpr (by exact_mod_cast h1)
    rw [div_lt_iff₀ ht]
    have := log_Q_le h1
    nlinarith

lemma Qr_le (h : ℕ) : Qr h ≤ ((h : ℝ) + 1) * pn h := by
  unfold Qr
  calc ∑ j ∈ range (h + 1), (pn j : ℝ) ≤ ∑ _j ∈ range (h + 1), (pn h : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        exact_mod_cast pn_monotone (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
    _ = ((h : ℝ) + 1) * pn h := by simp

lemma pn_le_Qr (h : ℕ) : (pn h : ℝ) ≤ Qr h := by
  unfold Qr
  exact Finset.single_le_sum (f := fun j => (pn j : ℝ)) (fun _ _ => by positivity)
    (Finset.mem_range.mpr (Nat.lt_succ_self h))

lemma tendsto_log_div_sqrt : Tendsto (fun x : ℝ => Real.log x / Real.sqrt x) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with x _
  rw [Real.sqrt_eq_rpow]

lemma tendsto_log_succ_div_sqrt :
    Tendsto (fun h : ℕ => Real.log ((h : ℝ) + 1) / Real.sqrt h) atTop (𝓝 0) := by
  have h1 : Tendsto (fun h : ℕ => (h : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have h3 := (tendsto_log_div_sqrt.comp h1).const_mul (Real.sqrt 2)
  rw [mul_zero] at h3
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h3
  · filter_upwards [eventually_ge_atTop 1] with h _
    exact div_nonneg (Real.log_nonneg (by linarith [(Nat.cast_nonneg h : (0 : ℝ) ≤ h)]))
      (Real.sqrt_nonneg _)
  · filter_upwards [eventually_ge_atTop 1] with h hh
    have hh' : (1 : ℝ) ≤ h := by exact_mod_cast hh
    have hL0 : 0 ≤ Real.log ((h : ℝ) + 1) := Real.log_nonneg (by linarith)
    have ht : 0 < Real.sqrt h := Real.sqrt_pos.mpr (by linarith)
    have ht1 : 0 < Real.sqrt ((h : ℝ) + 1) := Real.sqrt_pos.mpr (by linarith)
    have hs : Real.sqrt ((h : ℝ) + 1) ≤ Real.sqrt 2 * Real.sqrt h := by
      rw [← Real.sqrt_mul (by norm_num)]
      exact Real.sqrt_le_sqrt (by linarith)
    show Real.log ((h : ℝ) + 1) / Real.sqrt h ≤
      Real.sqrt 2 * (Real.log ((h : ℝ) + 1) / Real.sqrt ((h : ℝ) + 1))
    rw [mul_div_assoc', div_le_div_iff₀ ht ht1]
    nlinarith [mul_le_mul_of_nonneg_left hs hL0]

lemma tendsto_log_p :
    Tendsto (fun h : ℕ => Real.log (pn h) / Real.sqrt h) atTop (𝓝 (2 * Real.sqrt Isum)) := by
  have hQ := tendsto_log_Q
  have hL := tendsto_log_succ_div_sqrt
  have hlow : Tendsto (fun h : ℕ => Real.log (Qr h) / Real.sqrt h -
      Real.log ((h : ℝ) + 1) / Real.sqrt h) atTop (𝓝 (2 * Real.sqrt Isum)) := by
    simpa using hQ.sub hL
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hQ ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with h h1
    have ht : 0 < Real.sqrt h := Real.sqrt_pos.mpr (by exact_mod_cast h1)
    rw [← sub_div]
    apply div_le_div_of_nonneg_right _ ht.le
    have hp : (0 : ℝ) < pn h := by exact_mod_cast one_le_pn h
    have h2 : Real.log (Qr h) ≤ Real.log (((h : ℝ) + 1) * pn h) :=
      Real.log_le_log (lt_of_lt_of_le hp (pn_le_Qr h)) (Qr_le h)
    rw [Real.log_mul (by positivity) hp.ne'] at h2
    linarith
  · filter_upwards [eventually_ge_atTop 1] with h h1
    have ht : 0 < Real.sqrt h := Real.sqrt_pos.mpr (by exact_mod_cast h1)
    apply div_le_div_of_nonneg_right _ ht.le
    have hp : (0 : ℝ) < pn h := by exact_mod_cast one_le_pn h
    exact Real.log_le_log hp (pn_le_Qr h)

end OM.NNN30.Partition

