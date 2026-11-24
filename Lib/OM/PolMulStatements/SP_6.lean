/- Adapted from PLATFORM/Statements/SP.6.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMulStatements.DEF_1
import Lib.OM.PolMulStatements.DEF_10
import Lib.OM.PolMulStatements.DEF_19
import Lib.OM.PolMulStatements.DEF_20
import Lib.OM.PolMulStatements.DEF_21

open OM.PolMulDef

universe u

def OM_S_SP_6 : Prop :=
  ∀ (F : Type u) [Field F] (π : Equiv.Perm (Fin 3))
    (φ : Spectral F) {d : Fin 3 → ℕ+} (T : T3 F d),
      Spectral.eval (Spectral.perm π φ) T = Spectral.eval φ (perm π T)
