/- Adapted from PolMul/SpectralFacts.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMul.DegenAsymp
import Lib.OM.PolMul.SpectralFacts.SP5
import Lib.OM.PolMul.OmegaBridge
import Lib.OM.PolMulStatements.SP_1

namespace OM.PolMul.SpectralFacts

open AsymptoticSpectrumDuality
open Semicontinuity
open OM.PolMulDef

universe u

/-- The spectral characterization of the square matrix-multiplication
exponent (Strassen's Theorem 3.8 together with Proposition 4.2). -/
theorem proof_SP_1 : OM_S_SP_1 := by
  intro F _
  let p := OmegaBridge.pF F
  let a := OmegaBridge.mmClass F
  haveI : Nontrivial (TensorClass F 3) := by
    refine ⟨1, 0, ?_⟩
    intro h
    apply p.not_rel_one_zero
    rw [h]
    exact p.refl 0
  letI : Nonempty (AsymptoticSpectrum p) := AsymptoticSpectrum.nonempty p
  have ha : ∃ φ : AsymptoticSpectrum p,
      1 ≤ AsymptoticSpectrum.eval p a φ := by
    let φ : AsymptoticSpectrum p := Classical.choice inferInstance
    refine ⟨φ, ?_⟩
    have hmono := AsymptoticSpectrum.eval_mono (OmegaBridge.pF F) φ
      (OmegaBridge.one_le_mmClass F)
    simpa [p, a, AsymptoticSpectrum.eval_one] using! hmono
  obtain ⟨φmax, hmax⟩ := p.asympRank_eq_max_spectrum a ha
  have homega : omegaF F =
      Real.logb 2 ((OmegaBridge.pF F).asympRank (OmegaBridge.mmClass F)) := by
    calc
      omegaF F = Real.logb 2 ((2 : ℝ) ^ omegaF F) := by
        rw [Real.logb_rpow (by norm_num) (by norm_num)]
      _ = Real.logb 2 ((OmegaBridge.pF F).asympRank (OmegaBridge.mmClass F)) :=
        congrArg (Real.logb 2) (two_rpow_omegaF F)
  constructor
  · refine ⟨φmax, ?_⟩
    change omegaF F = Real.logb 2
      (AsymptoticSpectrum.eval (OmegaBridge.pF F) (OmegaBridge.mmClass F) φmax)
    rw [homega, hmax]
  · intro x hx
    obtain ⟨φ, rfl⟩ := hx
    change Real.logb 2
        (AsymptoticSpectrum.eval (OmegaBridge.pF F) (OmegaBridge.mmClass F) φ) ≤
      omegaF F
    rw [homega]
    have heval_one := AsymptoticSpectrum.eval_mono (OmegaBridge.pF F) φ
      (OmegaBridge.one_le_mmClass F)
    have hevalpos : 0 < AsymptoticSpectrum.eval (OmegaBridge.pF F)
        (OmegaBridge.mmClass F) φ := by
      have hone : (1 : ℝ) ≤ AsymptoticSpectrum.eval (OmegaBridge.pF F)
          (OmegaBridge.mmClass F) φ := by
        simpa only [AsymptoticSpectrum.eval_one] using! heval_one
      exact zero_lt_one.trans_le hone
    exact (Real.logb_le_logb (b := 2) (by norm_num) hevalpos
      (zero_lt_one.trans_le (OmegaBridge.one_le_asympRank_mmClass F))).2
        ((OmegaBridge.pF F).spectralPoint_le_asympRank φ (OmegaBridge.mmClass F))

end OM.PolMul.SpectralFacts

