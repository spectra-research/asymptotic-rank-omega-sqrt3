/- Adapted from PLATFORM/Statements/PR.3.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMulStatements.DEF_4
import Lib.OM.PolMulStatements.DEF_5
import Lib.OM.PolMulStatements.DEF_11
import Lib.OM.PolMulStatements.DEF_19
import Lib.OM.PolMulStatements.DEF_20
import Mathlib.Analysis.SpecialFunctions.Log.Base

open OM.PolMulDef

universe u

def OM_S_PR_3 : Prop :=
  ∀ (F : Type u) [Field F] (φ : Spectral F),
    0 < Real.logb 2 (Spectral.eval φ (matMul 1 1 2)) →
    ∀ (a b : ℕ+),
      2 * Spectral.eval φ (polmul a b) ^
          ((1 : ℝ) / Real.logb 2 (Spectral.eval φ (matMul 1 1 2))) +
        Spectral.eval φ (swap23 (polmul a b)) ^
          ((1 : ℝ) / Real.logb 2 (Spectral.eval φ (matMul 1 1 2))) ≤
        Spectral.eval φ (polmul a (3 * b + a - 1)) ^
          ((1 : ℝ) / Real.logb 2 (Spectral.eval φ (matMul 1 1 2)))
