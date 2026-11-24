/- Adapted from PLATFORM/Statements/SA.2.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMulStatements.DEF_1
import Lib.OM.PolMulStatements.DEF_4
import Lib.OM.PolMulStatements.DEF_9
import Lib.OM.PolMulStatements.DEF_19
import Lib.OM.PolMulStatements.DEF_20
import Mathlib.Analysis.SpecialFunctions.Log.Base

open OM.PolMulDef
open scoped BigOperators

universe u

def OM_S_SA_2 : Prop :=
  ∀ (F : Type u) [Field F] (φ : Spectral F),
    0 < Real.logb 2 (Spectral.eval φ (matMul 1 1 2)) →
    ∀ (m : ℕ+) (d : Fin m → Fin 3 → ℕ+) (n : ℕ+)
      (h : ∀ i, d i 0 = n) (T : ∀ i, T3 F (d i)),
        (∑ i : Fin m,
            Spectral.eval φ (T i) ^
              ((1 : ℝ) / Real.logb 2 (Spectral.eval φ (matMul 1 1 2)))) ≤
          Spectral.eval φ (pdsumFamily d n h T) ^
            ((1 : ℝ) / Real.logb 2 (Spectral.eval φ (matMul 1 1 2)))
