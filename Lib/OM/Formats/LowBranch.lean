import Lib.OM.Formats.Prices
import Lib.OM.Formats.Rectangular
import Lib.OM.Formats.SpectralRate
import Lib.OM.Formats.IntegerRates
import Lib.OM.NNN32.Conclusion
import PLATFORM.Statements.«R116.3»
import PLATFORM.Statements.«NNN.47»

/-! # Matched matrix multiplication and the low branch of the format dichotomy -/

noncomputable section
namespace OM.Formats

open Foundations.PairUnitExponents NNN22 P2M.R115

theorem proof_R116_3 : S_R116_3 := by
  intro hg x y z T
  apply ((PolMul.OmegaBridge.pF ℂ).asympRel_iff_forall_spectrum _ _).mpr
  intro φ
  change PolMul.Spectral ℂ at φ
  change φ.eval T ≤ φ.eval (PolMul.matMul y x z)
  rw [Omega.eval_matMul]
  by_cases pos : 0 < φ.eval T
  · obtain ⟨h,hn,hs,h₀,h₁,h₂⟩ := tight_support (NNN32.proof_R113_23.mp hg) φ
    have H := log_eval_le_support φ h hn hs T pos
    rw [Fin.sum_univ_three] at H
    let lg (n : ℕ+) := Real.logb 2 (n:ℕ)
    have prodlog (a b : ℕ+) : lg (a*b) = lg a + lg b := by
      dsimp only [lg]
      rw [PNat.mul_coe,Nat.cast_mul,Real.logb_mul (by positivity) (by positivity)]
    change _ ≤ h 0*lg (x*y) + h 1*lg (x*z) + h 2*lg (y*z) at H
    simp only [prodlog] at H
    apply (Real.logb_le_logb one_lt_two pos (by positivity)).mp
    rw [Real.logb_mul (by positivity) (by positivity),Real.logb_mul (by positivity) (by positivity)]
    simp only [Real.logb_rpow_eq_mul_logb_of_pos (show (0:ℝ) < (x:ℕ) by positivity),
      Real.logb_rpow_eq_mul_logb_of_pos (show (0:ℝ) < (y:ℕ) by positivity),
      Real.logb_rpow_eq_mul_logb_of_pos (show (0:ℝ) < (z:ℕ) by positivity),← h₀,← h₁,← h₂]
    exact H.trans_eq (by dsimp only [lg]; ring)
  · exact (not_lt.mp pos).trans (by positivity)

theorem proof_NNN_47 : S_NNN_47 := by
  intro hg a b c ha hab hbc ht s
  have hb := ha.trans_le hab
  have hc := hb.trans_le hbc
  have hx : 0 < s-a := by dsimp [s]; linarith
  have hy : 0 < s-b := by dsimp [s]; linarith
  have hz : 0 < s-c := by dsimp [s]; linarith
  apply le_antisymm
  · apply beta_le_of_price (y := ![a,b,c]) (fun i => by fin_cases i <;> assumption)
    intro φ
    obtain ⟨h,_,support,h₀,h₁,h₂⟩ := tight_support (NNN32.proof_R113_23.mp hg) φ
    apply (support ![a,b,c] (fun i => by fin_cases i <;> first | exact ha.le | exact hb.le | exact hc.le)).trans
    apply le_trans _ (NNN36.theta_dot_le_omegaRect3 φ hx.le hy.le hz.le)
    rw [Fin.sum_univ_three,← h₀,← h₁,← h₂]
    change h 0*a + h 1*b + h 2*c ≤ _
    dsimp only [s]; apply le_of_eq; ring
  · have H := rect_le_beta hx hy hz
    rwa [show s-b+(s-c) = a by dsimp [s]; ring,
      show s-c+(s-a) = b by dsimp [s]; ring,show s-a+(s-b) = c by dsimp [s]; ring] at H

/-- The integer-power formulation, with an ordinary limit and no rounding on the left. -/
theorem integer_low_limit (hg : P2M.R113.gamma = 1) (m n p : ℕ+) (hmn : m ≤ n) (hnp : n ≤ p)
    (ht : Real.logb 2 (p:ℕ) < Real.logb 2 (m:ℕ) + Real.logb 2 (n:ℕ)) :
    let a := Real.logb 2 (m:ℕ)
    let b := Real.logb 2 (n:ℕ)
    let c := Real.logb 2 (p:ℕ)
    let s := (a+b+c)/2
    Filter.Tendsto (fun t : ℕ => Real.logb 2 (formatRankSup (m^t) (n^t) (p^t))/t)
      Filter.atTop (nhds (OmegaBound.omegaRect3 ℂ (s-a) (s-b) (s-c))) := by
  intro a b c s
  have hab : a ≤ b := Real.logb_le_logb_of_le one_lt_two (by positivity) (by exact_mod_cast hmn)
  have hbc : b ≤ c := Real.logb_le_logb_of_le one_lt_two (by positivity) (by exact_mod_cast hnp)
  have H := integer_format_limit m n p
  rw [proof_NNN_47 hg a b c (by change c < a+b at ht; linarith) hab hbc ht] at H
  exact H

end OM.Formats

