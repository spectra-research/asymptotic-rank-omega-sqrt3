import Lib.OM.NNN36.Plateau
import PLATFORM.Statements.«R115.6»

/-! # Exact asymptotic rank on the isosceles strip -/

namespace OM.NNN36

open P2M.R115

/-- In the normalized isosceles triangle the cubic root is the midpoint.
The lower bound on the longest side puts the altitude at most one quarter. -/
private theorem midpoint_test {a c : ℝ} (hc : 0 < c) (hsq : 16*a^2 ≤ 5*c^2) :
    let q := normalizedApex a a c
    (3*(1/2 : ℝ)^2-2*(1/2 : ℝ)^3 = q.re) ∧
      ((1/2 : ℝ)-q.re)^2 + q.im^2 ≤ (1/2 : ℝ)^2*(1-1/2)^2 := by
  let q := normalizedApex a a c
  have hre : q.re = 1/2 := by
    change (a^2+c^2-a^2)/(2*c^2) = 1/2
    field_simp
    ring
  have him : q.im ≤ 1/4 := by
    change Real.sqrt ((a/c)^2 - q.re^2) ≤ 1/4
    rw [hre, Real.sqrt_le_iff]
    refine ⟨by norm_num, ?_⟩
    rw [div_pow]
    have hrat : a^2/c^2 ≤ 5/16 := (div_le_iff₀ (sq_pos_of_pos hc)).mpr (by linarith)
    linarith
  have hsqim := pow_le_pow_left₀ (show 0 ≤ q.im from Real.sqrt_nonneg _) him 2
  change (_ = q.re) ∧ (_ + q.im^2 ≤ _)
  rw [hre]
  constructor
  · norm_num
  · nlinarith only [hsqim]

theorem proof_R115_6 : S_R115_6 := by
  intro n m hlo hhi
  let a := sideLog n
  let c := sideLog m
  have hs : 0 < Real.sqrt 5 := by positivity
  have hs2 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hpow : (1 : ℝ) ≤ 4/Real.sqrt 5 := (le_div_iff₀ hs).mpr (by nlinarith only [hs2])
  have hn : 1 ≤ (n : ℝ) := by exact_mod_cast n.pos
  have hnm : n ≤ m := by
    have h := (Real.rpow_le_rpow_of_exponent_le hn hpow).trans hlo
    rw [Real.rpow_one] at h
    exact_mod_cast h
  have hlog : Real.logb 2 ((n : ℝ)^2) = a+a := by
    rw [Real.logb_pow]
    change (2 : ℝ)*a = a+a
    ring
  rcases hhi.lt_or_eq with hlt | heq
  · have ht : c < a+a := by
      rw [← hlog]
      exact (Real.logb_lt_logb_iff one_lt_two (by positivity) (by positivity)).mpr (by exact_mod_cast hlt)
    have hac : a ≤ c := sideLog_mono hnm
    have ha : 0 < a := by linarith
    have hc := ha.trans_le hac
    have hloglo := Real.logb_le_logb_of_le one_lt_two (by positivity) hlo
    rw [Real.logb_rpow_eq_mul_logb_of_pos (by positivity)] at hloglo
    change (4/Real.sqrt 5)*a ≤ c at hloglo
    have hm : 4*a ≤ c*Real.sqrt 5 := (div_le_iff₀ hs).mp (by
      rw [← mul_div_right_comm] at hloglo
      exact hloglo)
    have hsq := pow_le_pow_left₀ (show 0 ≤ 4*a by positivity) hm 2
    rw [mul_pow, mul_pow, hs2] at hsq
    obtain ⟨he,htest⟩ := midpoint_test hc (show 16*a^2 ≤ 5*c^2 by nlinarith only [hsq])
    exact (proof_R115_5 n n m le_rfl hnm ht).2 (1/2) ⟨by constructor <;> norm_num, he⟩ htest
  · have hval : (m : ℝ) = (n : ℝ)^2 := by exact_mod_cast heq
    have ht : a+a ≤ c := by change a+a ≤ Real.logb 2 (m : ℝ); rw [hval, hlog]
    have h := proof_R115_3 n n m le_rfl hnm ht
    rw [hval, pow_two]
    exact h

end OM.NNN36

