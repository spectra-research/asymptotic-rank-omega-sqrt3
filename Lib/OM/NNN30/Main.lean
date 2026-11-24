import Lib.OM.NNN30.RectMain
import Lib.OM.NNN30.Net.Main
import Lib.OM.NNN30.Geom.Main
import Lib.OM.NNN30.Final

/-! # The cube-format bound and its two registered specialisations -/

namespace OM.NNN30

open Foundations.PairUnitExponents

theorem proof_R111_2 : S_R111_2 := Net.metric_of proof_R108_3

theorem proof_R111_3 : S_R111_3 := Fin.cube_of Geom.proof_R111_1 proof_R111_2

theorem proof_NNN_30 : S_NNN_30 := Fin.nnn30_of proof_R111_3

theorem proof_NNN_31 : S_NNN_31 := Fin.nnn31_of proof_R111_3

/-- The cost of the three pair units is at most the actual matrix-multiplication exponent. -/
theorem sum_le_omega (φ : OM.PolMul.Spectral ℂ) :
    theta φ 0 + theta φ 1 + theta φ 2 ≤ OM.PolMul.omegaF ℂ := by
  have h := (OM.PolMul.SpectralFacts.proof_SP_1 ℂ).2 ⟨φ, rfl⟩
  change Real.logb 2 (OM.PolMul.Spectral.eval φ (OM.PolMul.matMul 2 2 2)) ≤ OM.PolMul.omegaF ℂ at h
  rw [OM.Omega.eval_matMul_square] at h
  simpa only [PNat.val_ofNat, Nat.cast_ofNat,
    Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)] using h

/-- The cube-format bound in terms of the true exponent, for every complex cube-format tensor. -/
theorem asympRank_le_omega_div_sqrt_three (n : ℕ+)
    (T : Semicontinuity.KTensor ℂ (fun _ : Fin 3 => n)) :
    Semicontinuity.asympRank T ≤ ((n : ℕ) : ℝ) ^ (OM.PolMul.omegaF ℂ / Real.sqrt 3) := by
  obtain ⟨ψ, _⟩ := (OM.PolMul.SpectralFacts.proof_SP_1 ℂ).1
  have hω : 0 < OM.PolMul.omegaF ℂ :=
    (by norm_num : (0 : ℝ) < 2).trans_le ((two_le_theta_sum ψ).trans (sum_le_omega ψ))
  apply OM.NNN22.proof_R88_17 _ (div_pos hω (Real.sqrt_pos.2 (by norm_num))) _ n T
  intro φ _ _ _ _
  rw [le_div_iff₀ (Real.sqrt_pos.2 (by norm_num)), mul_comm]
  exact (proof_R111_3 φ).trans (sum_le_omega φ)

end OM.NNN30

