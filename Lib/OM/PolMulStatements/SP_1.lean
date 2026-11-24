/- Adapted from PLATFORM/Statements/SP.1.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMulStatements.DEF_4
import Lib.OM.PolMulStatements.DEF_16
import Lib.OM.PolMulStatements.DEF_19
import Lib.OM.PolMulStatements.DEF_20
import Mathlib.Analysis.SpecialFunctions.Log.Base

open OM.PolMulDef

universe u

def OM_S_SP_1 : Prop :=
  ∀ (F : Type u) [Field F],
    IsGreatest
      {x : ℝ | ∃ φ : Spectral F,
        x = Real.logb 2 (Spectral.eval φ (matMul 2 2 2))}
      (omegaF F)
