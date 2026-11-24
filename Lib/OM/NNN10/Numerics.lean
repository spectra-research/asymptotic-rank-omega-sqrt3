import Lib.OM.NNN8.Numerics

noncomputable section
namespace OM.NNN10

def beta : ℝ := 17 / 16 + 1 / 4 * Real.logb 2 (1 + (2 : ℝ) ^ (3 / 4 : ℝ))

def codeC (t : ℝ) : ℝ := 13 / 4 - 2 * t - NNN8.codeG t

lemma beta_eq : beta = 3 / 2 - codeC (3 / 4) / 4 := by
  norm_num [beta, codeC, NNN8.codeG]
  ring

theorem beta_lt : beta < 1419 / 1000 := by
  have hg := NNN8.codeG_three_quarters_lt
  norm_num [NNN8.codeG] at hg
  dsimp [beta]
  linarith

lemma beta_nonneg : 0 ≤ beta := by
  have hg : 0 ≤ Real.logb 2 (1 + (2 : ℝ) ^ (3 / 4 : ℝ)) :=
    Real.logb_nonneg (by norm_num)
      (le_add_of_nonneg_right (Real.rpow_nonneg (by norm_num) _))
  dsimp [beta]
  linarith

lemma codeC_balance_pos : 0 < codeC (3 / 4) := by
  have h := beta_lt
  rw [beta_eq] at h
  linarith

lemma beta_lt_three_halves : beta < 3 / 2 := by linarith [beta_lt]

end OM.NNN10
