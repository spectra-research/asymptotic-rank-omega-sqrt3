/- Adapted from PLATFORM/Statements/SP.2.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMulStatements.DEF_1
import Lib.OM.PolMulStatements.DEF_12
import Lib.OM.PolMulStatements.DEF_19
import Lib.OM.PolMulStatements.DEF_20

open OM.PolMulDef

universe u

def OM_S_SP_2 : Prop :=
  ∀ (F : Type u) [Field F] (φ : Spectral F)
    {dT dS : Fin 3 → ℕ+} (T : T3 F dT) (S : T3 F dS),
      Degen T S → Spectral.eval φ T ≤ Spectral.eval φ S
