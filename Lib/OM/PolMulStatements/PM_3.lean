/- Adapted from PLATFORM/Statements/PM.3.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMulStatements.DEF_1
import Lib.OM.PolMulStatements.DEF_4
import Lib.OM.PolMulStatements.DEF_7
import Lib.OM.PolMulStatements.DEF_9
import Lib.OM.PolMulStatements.DEF_24

open OM.PolMulDef

universe u

def OM_S_PM_3 : Prop :=
  ∀ (F : Type u) [Field F] {d : Fin 3 → ℕ+}
    (T : T3 F d) (k : ℕ+),
      Iso
        (pdsumFamily (fun _ : Fin k => d) (d 0) (fun _ => rfl) (fun _ => T))
        (kron T (matMul 1 1 k))
