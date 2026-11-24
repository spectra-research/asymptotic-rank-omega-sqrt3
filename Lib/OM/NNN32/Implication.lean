import Lib.OM.NNN32.Metric
import Lib.OM.NNN32.Sectors
import Lib.OM.NNN30.Main
import PLATFORM.Statements.«R113.11»
import PLATFORM.Statements.«R113.12»
import PLATFORM.Statements.«NNN.32»
import PLATFORM.Statements.«NNN.33»

/-! # From a finite crossing saving to the all-tensor bound -/

namespace OM.NNN32

open Foundations.PairUnitExponents

theorem proof_R113_11 : S_R113_11 := by
  intro hw φ
  obtain ⟨c,hc,hu,h⟩ := proof_R113_9 hw
  obtain ⟨X,S,p,o,hl,hmin,hs,h12,h02,h01⟩ := h φ
  have hh := proof_R113_10 X S c hc hu hl p o (fun q => hs.le.trans (hmin q))
  rw [hh 1 2 (by decide +kernel)] at h12
  rw [hh 0 2 (by decide +kernel)] at h02
  rw [hh 0 1 (by decide +kernel)] at h01
  rw [Fin.sum_univ_three] at hs
  linarith

theorem proof_R113_12 : S_R113_12 := by
  intro hw
  obtain ⟨ψ,_⟩ := (OM.PolMul.SpectralFacts.proof_SP_1 ℂ).1
  have hω : 0 < OM.PolMul.omegaF ℂ :=
    (by norm_num : (0 : ℝ) < 2).trans_le ((two_le_theta_sum ψ).trans (OM.NNN30.sum_le_omega ψ))
  refine OM.NNN22.proof_R88_17 _ (half_pos hω) ?_
  intro φ _ _ _ _
  linarith [(proof_R113_11 hw φ).trans (OM.NNN30.sum_le_omega φ)]

theorem proof_NNN_32 : S_NNN_32 := by
  intro hw n T
  apply (proof_R113_12 hw n T).trans
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast n.2)
  linarith [OM.Omega.omega_le_nine_quarters (F := ℂ)]

theorem proof_NNN_33 : S_NNN_33 := by
  intro hw hω n T
  have h := proof_R113_12 hw n T
  rwa [hω,div_self (by norm_num : (2 : ℝ) ≠ 0),Real.rpow_one] at h

end OM.NNN32
