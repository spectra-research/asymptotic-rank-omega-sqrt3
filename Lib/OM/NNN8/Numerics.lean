import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

/-! Exact rational certificates for the Route 1 endpoint and derivative bounds. -/
noncomputable section
namespace OM.NNN8
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1000

def codeG (t : ℝ) : ℝ := Real.logb 2 (1 + (2 : ℝ) ^ (9 / 4 - 2 * t))
def codeExponent (t : ℝ) : ℝ := 9 / 4 + t / (1 + t) * codeG t
def alpha0 : ℝ := 9 / 8 + 3 / 14 * Real.logb 2 (1 + (2 : ℝ) ^ (3 / 4 : ℝ))

lemma rational_certificates :
    (19 / 16 : ℝ) ^ (4 : ℕ) < 2 ∧
    2 < (11893 / 10000 : ℝ) ^ (4 : ℕ) ∧
    (1 + (11893 / 10000 : ℝ) ^ (3 : ℕ)) ^ (40 : ℕ) < (2 : ℝ) ^ (57 : ℕ) ∧
    2 < (118921 / 100000 : ℝ) ^ (4 : ℕ) ∧
    (1 + (118921 / 100000 : ℝ) ^ (3 : ℕ)) ^ (300 : ℕ) < (2 : ℝ) ^ (427 : ℕ) := by
  norm_num

lemma lt_two_rpow_of_pow_lt {x : ℝ} (hx : 0 ≤ x) {p q : ℕ} (hq : 0 < q)
    (h : x ^ q < (2 : ℝ) ^ p) : x < (2 : ℝ) ^ ((p : ℝ) / q) := by
  have he : ((2 : ℝ) ^ ((p : ℝ) / q)) ^ q = (2 : ℝ) ^ p := by
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2),
      div_mul_cancel₀ _ (by exact_mod_cast hq.ne'), Real.rpow_natCast]
  apply (pow_lt_pow_iff_left₀ hx (by positivity) hq.ne').mp
  rwa [he]

lemma fourth_root_lt {v : ℝ} (hv : 0 ≤ v) (h : 2 < v ^ (4 : ℕ)) :
    (2 : ℝ) ^ (1 / 4 : ℝ) < v := by
  apply (pow_lt_pow_iff_left₀ (by positivity) hv (by norm_num : 4 ≠ 0)).mp
  rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num
  exact h

lemma three_quarters_lt_cube {v : ℝ} (hv : 0 ≤ v) (h : 2 < v ^ (4 : ℕ)) :
    (2 : ℝ) ^ (3 / 4 : ℝ) < v ^ (3 : ℕ) := by
  have hroot := fourth_root_lt hv h
  have he : (2 : ℝ) ^ (3 / 4 : ℝ) = ((2 : ℝ) ^ (1 / 4 : ℝ)) ^ (3 : ℕ) := by
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [he]
  gcongr

lemma codeG_three_quarters_lt : codeG (3 / 4) < 57 / 40 := by
  have hx := three_quarters_lt_cube (by norm_num : (0 : ℝ) ≤ 11893 / 10000)
    rational_certificates.2.1
  have hy := lt_two_rpow_of_pow_lt
    (by positivity : (0 : ℝ) ≤ 1 + (11893 / 10000 : ℝ) ^ (3 : ℕ))
    (by norm_num : 0 < 40) rational_certificates.2.2.1
  dsimp [codeG]
  norm_num only [show (9 / 4 - 2 * (3 / 4) : ℝ) = 3 / 4 by norm_num]
  apply (Real.logb_lt_iff_lt_rpow (by norm_num : (1 : ℝ) < 2) (by positivity)).2
  exact (add_lt_add_of_le_of_lt (le_refl (1 : ℝ)) hx).trans hy

lemma fourth_root_lower : (19 / 16 : ℝ) < (2 : ℝ) ^ (1 / 4 : ℝ) := by
  simpa using! lt_two_rpow_of_pow_lt (x := 19 / 16) (p := 1) (by norm_num) (by norm_num : 0 < 4)
    (by simpa using! rational_certificates.1)

theorem alpha0_lt : alpha0 < 143 / 100 := by
  have hx := three_quarters_lt_cube (by norm_num : (0 : ℝ) ≤ 118921 / 100000)
    rational_certificates.2.2.2.1
  have hy := lt_two_rpow_of_pow_lt
    (by positivity : (0 : ℝ) ≤ 1 + (118921 / 100000 : ℝ) ^ (3 : ℕ))
    (by norm_num : 0 < 300) rational_certificates.2.2.2.2
  have hg : Real.logb 2 (1 + (2 : ℝ) ^ (3 / 4 : ℝ)) < 427 / 300 := by
    apply (Real.logb_lt_iff_lt_rpow (by norm_num : (1 : ℝ) < 2) (by positivity)).2
    exact (add_lt_add_of_le_of_lt (le_refl (1 : ℝ)) hx).trans hy
  dsimp [alpha0]
  linarith

lemma codeExponent_three_quarters : codeExponent (3 / 4) = 2 * alpha0 := by
  norm_num [codeExponent, codeG, alpha0]
  ring

end OM.NNN8
