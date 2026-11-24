import Lib.OM.Formats.LowBranch
import Lib.OM.Formats.HighBranch
import PLATFORM.Statements.«NNN.50»
import PLATFORM.Statements.«NNN.51»
import Lib.OM.PolMulRect.Flat

/-! # Distinguishing the crossing branches in the (3,3,4) format -/

namespace OM.Formats

private theorem diameter_334 : 2 * P2M.R116.discRadius 3 3 4 = 9 / Real.sqrt 5 := by
  have sqrt20 : Real.sqrt 20 = 2 * Real.sqrt 5 := by
    rw [show (20:ℝ)=4*5 by norm_num,Real.sqrt_mul (by norm_num)]; norm_num
  norm_num [P2M.R116.discRadius,sqrt20]
  ring

theorem proof_NNN_51 : S_NNN_51 := by
  intro hg
  rw [← diameter_334]
  exact proof_NNN_48 hg 3 3 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem proof_NNN_50 : S_NNN_50 := by
  constructor
  · intro hg
    have H := proof_NNN_47 hg 3 3 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    norm_num at H
    rw [PolMulRect.omegaRect3_eq_omegaRect,
      PolMulRect.omegaRect_eq_add ℂ (by norm_num) (by norm_num) (by norm_num) (by norm_num)] at H
    norm_num at H
    exact H
  · intro he
    rcases NNN32.proof_R113_22.1 with hg | hg
    · exact hg
    · have H := proof_NNN_51 hg
      rw [he,div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num))] at H
      nlinarith only [Real.sq_sqrt (by norm_num : 0 ≤ (5:ℝ)),
        mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 9) H]

/-- The exponent at (3,3,4) is four exactly when every positive integer
base attains its fourth power as the maximal asymptotic rank. -/
theorem exponent_334_iff_formatRank :
    P2M.R116.formatBeta 3 3 4 = 4 ↔
      ∀ t : ℕ+, P2M.R115.formatRankSup (t^3) (t^3) (t^4) = (t : ℝ)^4 := by
  constructor
  · intro hβ t
    obtain ⟨lower, upper⟩ := NNN36.format_bounds (t^3) (t^3) (t^4)
    have fit : (t : ℕ)^4 ≤ (t : ℕ)^3 * (t : ℕ)^3 := by
      rw [← pow_add]
      exact Nat.pow_le_pow_right t.pos (by decide)
    simp only [PNat.pow_coe, min_eq_left fit, Nat.cast_pow] at lower
    refine le_antisymm ?_ lower
    by_cases ht : 2 ≤ t
    · apply csSup_le (Set.range_nonempty _)
      rintro _ ⟨T, rfl⟩
      by_cases hT : 0 < Semicontinuity.asympRank T
      · have bound := log_rank_le_beta (y := ![3, 3, 4])
          (by intro i; fin_cases i <;> norm_num) T ht
          (by intro i; fin_cases i <;> norm_num [PolMul.fmt]) hT
        change Real.logb (t : ℕ) (Semicontinuity.asympRank T) ≤ P2M.R116.formatBeta 3 3 4 at bound
        simpa using (Real.logb_le_iff_le_rpow (cast_one_lt t ht) hT).mp (bound.trans_eq hβ)
      · exact (not_lt.mp hT).trans (by positivity)
    · have ht₁ : (t : ℕ) = 1 := by
        change ¬ 2 ≤ (t : ℕ) at ht
        have := t.pos
        omega
      exact upper.trans (by simp [ht₁])
  · intro ranks
    have dim_pow (t : ℕ+) (k : ℕ) : dim t k = t^k := by
      apply PNat.eq
      change ⌈((t : ℕ) : ℝ) ^ (k : ℝ)⌉₊ = (t : ℕ)^k
      rw [Real.rpow_natCast, ← Nat.cast_pow, Nat.ceil_natCast]
    change Filter.limsup (baseRate 3 3 4) Filter.atTop = 4
    refine (Filter.limsup_congr (v := fun _ => (4 : ℝ)) ?_).trans (Filter.limsup_const 4)
    filter_upwards [Filter.eventually_ge_atTop (2 : ℕ+)] with t ht
    change Real.logb (t : ℕ) (P2M.R115.formatRankSup (dim t (3 : ℕ)) (dim t (3 : ℕ))
      (dim t (4 : ℕ))) = 4
    rw [dim_pow, dim_pow, ranks, Real.logb_pow, Real.logb_self_eq_one (cast_one_lt t ht)]
    norm_num

end OM.Formats

