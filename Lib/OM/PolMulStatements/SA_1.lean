/- Adapted from PLATFORM/Statements/SA.1.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMulStatements.DEF_1
import Lib.OM.PolMulStatements.DEF_4
import Lib.OM.PolMulStatements.DEF_9
import Lib.OM.PolMulStatements.DEF_19
import Lib.OM.PolMulStatements.DEF_20
import Lib.OM.PolMulStatements.DEF_24
import Mathlib.Analysis.SpecialFunctions.Log.Base

open OM.PolMulDef

universe u

def OM_S_SA_1 : Prop :=
  ∀ (F : Type u) [Field F] (φ : Spectral F),
    0 < Real.logb 2 (Spectral.eval φ (matMul 1 1 2)) →
    ∀ (r : ℕ+) (d : Fin r → Fin 3 → ℕ+) (n : ℕ+)
      (h : ∀ i, d i 0 = n) (S : ∀ i, T3 F (d i)),
        (∀ i, Iso (S i) (S 0)) →
        (1 / 2 : ℝ) *
            (((r : ℕ) : ℝ) ^
              Real.logb 2 (Spectral.eval φ (matMul 1 1 2))) *
            Spectral.eval φ (S 0) ≤
          Spectral.eval φ (pdsumFamily d n h S)
