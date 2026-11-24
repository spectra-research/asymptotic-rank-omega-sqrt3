/- Adapted from PLATFORM/Statements/PR.2.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMulStatements.DEF_4
import Lib.OM.PolMulStatements.DEF_5
import Lib.OM.PolMulStatements.DEF_19
import Lib.OM.PolMulStatements.DEF_20
import Mathlib.Analysis.SpecialFunctions.Log.Base

open OM.PolMulDef

universe u

def OM_S_PR_2 : Prop :=
  ∀ (F : Type u) [Field F] (φ : Spectral F),
    0 < Real.logb 2 (Spectral.eval φ (matMul 1 1 2)) →
    ∀ (a m : ℕ+), 2 ≤ m →
      Spectral.eval φ (polmul a (m + 1)) ^
          ((1 : ℝ) / Real.logb 2 (Spectral.eval φ (matMul 1 1 2))) +
        Spectral.eval φ (polmul a (m - 1)) ^
          ((1 : ℝ) / Real.logb 2 (Spectral.eval φ (matMul 1 1 2))) ≤
        2 * Spectral.eval φ (polmul a m) ^
          ((1 : ℝ) / Real.logb 2 (Spectral.eval φ (matMul 1 1 2)))
