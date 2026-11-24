/- Adapted from PLATFORM/Statements/AN.3.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMulStatements.DEF_4
import Lib.OM.PolMulStatements.DEF_5
import Lib.OM.PolMulStatements.DEF_10
import Lib.OM.PolMulStatements.DEF_19
import Lib.OM.PolMulStatements.DEF_20
import Mathlib.Analysis.SpecialFunctions.Log.Base

open OM.PolMulDef
open scoped BigOperators

universe u

def OM_S_AN_3 : Prop :=
  ∀ (F : Type u) [Field F] (φ : Spectral F) (n : ℕ+),
    (((n : ℕ) : ℝ) ^
        (8 * Real.logb 2 (Spectral.eval φ (matMul 2 2 2)) / 3)) ≤
      ∏ π : Equiv.Perm (Fin 3), Spectral.eval φ (perm π (polmul n n))
