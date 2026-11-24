/- Adapted from PolMul/Superadditivity/Rate.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMul.DegenAsymp.Rate

/-! # Removing polynomial overhead from power inequalities -/

namespace OM.PolMul.Superadditivity

open Filter
open scoped Topology

/-- The polynomial number of types and a fixed positive constant have root
limit one. This reuses the linear-root limit for degenerations. -/
lemma tendsto_type_overhead (m : ℕ) {C : ℝ} (hC : 0 < C) :
    Tendsto (fun k : ℕ => C ^ (1 / (k : ℝ)) *
      (((k + 1 : ℕ) : ℝ) ^ (1 / (k : ℝ))) ^ m) atTop (nhds 1) := by
  have h₁ : Tendsto (fun k : ℕ => C ^ (1 / (k : ℝ))) atTop (nhds 1) := by
    simpa using! (tendsto_const_nhds.rpow tendsto_one_div_atTop_nhds_zero_nat
      (Or.inl hC.ne'))
  have h₂ : Tendsto (fun k : ℕ =>
      (((k + 1 : ℕ) : ℝ) ^ (1 / (k : ℝ))) ^ m) atTop (nhds 1) := by
    simpa using! (DegenAsymp.tendsto_linear_root 1).pow m
  simpa using! h₁.mul h₂

/-- A fixed polynomial overhead cannot increase the exponential growth rate. -/
lemma le_of_power_le_polynomial {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hC : 0 < C) (m : ℕ)
    (h : ∀ k : ℕ, 1 ≤ k → A ^ k ≤ C * ((k + 1 : ℕ) : ℝ) ^ m * B ^ k) :
    A ≤ B := by
  have hlim := (tendsto_type_overhead m hC).mul_const B
  simp only [one_mul] at hlim
  apply ge_of_tendsto hlim
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hr := Real.rpow_le_rpow (pow_nonneg hA k) (h k hk)
    (by positivity : (0 : ℝ) ≤ 1 / (k : ℝ))
  rw [Real.mul_rpow (mul_nonneg hC.le (by positivity)) (pow_nonneg hB k),
    Real.mul_rpow hC.le (by positivity),
    ← Real.rpow_pow_comm (by positivity : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ)),
    one_div, Real.pow_rpow_inv_natCast hA (by omega),
    Real.pow_rpow_inv_natCast hB (by omega)] at hr
  simpa only [one_div] using! hr

end OM.PolMul.Superadditivity

