/- Adapted from PLATFORM/Statements/SP.5.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMulStatements.DEF_4
import Lib.OM.PolMulStatements.DEF_19
import Lib.OM.PolMulStatements.DEF_20
import Mathlib.Analysis.SpecialFunctions.Log.Base

open OM.PolMulDef

universe u

def OM_S_SP_5 : Prop :=
  ∀ (F : Type u) [Field F] (φ : Spectral F),
    (1 ≤ Spectral.eval φ (matMul 1 1 2) ∧
      Spectral.eval φ (matMul 1 1 2) ≤ 2) ∧
    (1 ≤ Spectral.eval φ (matMul 2 1 1) ∧
      Spectral.eval φ (matMul 2 1 1) ≤ 2) ∧
    (1 ≤ Spectral.eval φ (matMul 1 2 1) ∧
      Spectral.eval φ (matMul 1 2 1) ≤ 2) ∧
    ∀ n₁ n₂ n₃ : ℕ+,
      Spectral.eval φ (matMul n₁ n₂ n₃) =
        Spectral.eval φ (matMul 2 1 1) ^
            Real.logb 2 (((n₁ : ℕ) : ℝ)) *
        Spectral.eval φ (matMul 1 2 1) ^
            Real.logb 2 (((n₂ : ℕ) : ℝ)) *
        Spectral.eval φ (matMul 1 1 2) ^
            Real.logb 2 (((n₃ : ℕ) : ℝ))
