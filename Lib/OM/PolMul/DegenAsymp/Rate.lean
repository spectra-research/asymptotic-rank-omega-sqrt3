/- Adapted from PolMul/DegenAsymp/Rate.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMul.Defs
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# The quadratic overhead has exponential rate one

The linear-root limit adapts the private `tendsto_overhead_rpow` proof in
`AsymptoticSubrank/BorderSubrank.lean` (Apache-2.0).
-/

namespace OM.PolMul.DegenAsymp

open Filter AsymptoticSpectrumDuality
open scoped Topology

lemma tendsto_linear_root (N : ℕ) :
    Filter.Tendsto (fun n : ℕ => ((N * n + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / (n : ℝ)))
      Filter.atTop (nhds 1) := by
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · -- `N = 0`: the function is `1^{1/n} = 1`, constantly.
    subst hN0
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards with n
    simp
  · -- `N ≥ 1`: `(N·n+1)^{1/n} = exp((1/n)·log(N·n+1))` and `(1/n)·log(N·n+1) → 0`.
    -- `log(N·n+1)/n → 0`.
    have hlog : Filter.Tendsto
        (fun n : ℕ => Real.log ((N * n + 1 : ℕ) : ℝ) * ((1 : ℝ) / (n : ℝ)))
        Filter.atTop (nhds 0) := by
      -- `log` is little-o of `id`, so `log x / x → 0`; precompose with `x = N·n+1 → ∞`.
      have hdiv : Filter.Tendsto (fun x : ℝ => Real.log x / x) Filter.atTop (nhds 0) := by
        have := Real.isLittleO_log_id_atTop
        simpa [div_eq_mul_inv] using!
          (Asymptotics.IsLittleO.tendsto_div_nhds_zero this)
      have hAt : Filter.Tendsto (fun n : ℕ => ((N * n + 1 : ℕ) : ℝ))
          Filter.atTop Filter.atTop := by
        apply Filter.tendsto_atTop_mono (fun n => ?_) (tendsto_natCast_atTop_atTop (R := ℝ))
        · have h1N : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNpos
          push_cast
          nlinarith [Nat.cast_nonneg (α := ℝ) n]
      have hcomp : Filter.Tendsto
          (fun n : ℕ => Real.log ((N * n + 1 : ℕ) : ℝ) / ((N * n + 1 : ℕ) : ℝ))
          Filter.atTop (nhds 0) := hdiv.comp hAt
      -- `log(N·n+1) * (1/n) = (log(N·n+1)/(N·n+1)) * ((N·n+1)/n)` and `(N·n+1)/n → N`.
      have hratio : Filter.Tendsto (fun n : ℕ => ((N * n + 1 : ℕ) : ℝ) / (n : ℝ))
          Filter.atTop (nhds (N : ℝ)) := by
        have heq : (fun n : ℕ => ((N * n + 1 : ℕ) : ℝ) / (n : ℝ))
            =ᶠ[Filter.atTop] (fun n : ℕ => (N : ℝ) + (1 : ℝ) / (n : ℝ)) := by
          filter_upwards [Filter.eventually_gt_atTop 0] with n hn
          have hn0 : (n : ℝ) ≠ 0 := by positivity
          push_cast
          field_simp
        rw [Filter.tendsto_congr' heq]
        have h1n : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) Filter.atTop (nhds 0) :=
          tendsto_one_div_atTop_nhds_zero_nat
        simpa using! (tendsto_const_nhds.add h1n)
      have hmul := hcomp.mul hratio
      rw [zero_mul] at hmul
      refine hmul.congr' ?_
      filter_upwards [Filter.eventually_gt_atTop 0] with n hn
      have hden : ((N * n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      have hn0 : (n : ℝ) ≠ 0 := by positivity
      field_simp
    -- `(N·n+1)^{1/n} = exp((1/n)·log(N·n+1))`, continuous `exp`, limit `exp 0 = 1`.
    have hpos : ∀ n : ℕ, (0 : ℝ) < ((N * n + 1 : ℕ) : ℝ) := fun n => by positivity
    have hrw : (fun n : ℕ => ((N * n + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / (n : ℝ)))
        =ᶠ[Filter.atTop]
        (fun n : ℕ => Real.exp (Real.log ((N * n + 1 : ℕ) : ℝ) * ((1 : ℝ) / (n : ℝ)))) := by
      filter_upwards with n
      rw [Real.rpow_def_of_pos (hpos n), mul_comm]
    rw [Filter.tendsto_congr' hrw]
    have := (Real.continuous_exp.tendsto 0).comp hlog
    simpa using! this


/-- The coefficient-extraction overhead is subexponential. -/
lemma tendsto_quadratic_root (q : ℕ) :
    Tendsto (fun n : ℕ => (((q*n+1)^2 : ℕ) : ℝ) ^ (1 / (n : ℝ))) atTop (nhds 1) := by
  have h : Tendsto (fun n : ℕ => (((q*n+1 : ℕ) : ℝ) ^ (1 / (n : ℝ))) ^ 2)
      atTop (nhds 1) := by simpa using! (tendsto_linear_root q).pow 2
  convert! h using 1
  funext n
  rw [Nat.cast_pow, ← Real.rpow_natCast_mul (by positivity),
    ← Real.rpow_mul_natCast (by positivity)]
  congr 1
  ring

/-- The exact infimum required by `AsympRel`, including `q=0`. -/
lemma quadratic_root_inf (q : ℕ) :
    sInf ((fun n : ℕ => (((q*n+1)^2 : ℕ) : ℝ) ^ (1 / (n : ℝ))) ''
      {n : ℕ | 1 ≤ n}) = 1 := by
  apply (sInf_eq_one_iff_tendsto (x := fun n => (q*n+1)^2)
    (fun n => by
      have hp : 0 < (q*n+1)^2 := by positivity
      exact hp) ?_).mpr (tendsto_quadratic_root q)
  intro n m
  change (q*(n+m)+1)^2 ≤ (q*n+1)^2 * (q*m+1)^2
  rw [← mul_pow]
  apply Nat.pow_le_pow_left _ 2
  nlinarith [Nat.zero_le (q*q*n*m)]

end OM.PolMul.DegenAsymp
