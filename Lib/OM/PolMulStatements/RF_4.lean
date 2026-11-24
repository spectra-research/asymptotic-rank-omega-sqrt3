/- Adapted from PLATFORM/Statements/RF.4.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMulStatements.DEF_3
import Lib.OM.PolMulStatements.DEF_6
import Lib.OM.PolMulStatements.DEF_7
import Lib.OM.PolMulStatements.DEF_10
import Lib.OM.PolMulStatements.DEF_24

open OM.PolMulDef
open Semicontinuity

universe u

def OM_S_RF_4 : Prop :=
  ∀ (F : Type u) [Field F] (π : Equiv.Perm (Fin 3))
    {dS dT : Fin 3 → ℕ+} (S : T3 F dS) (T : T3 F dT),
      Iso (perm π (dsum S T)) (dsum (perm π S) (perm π T)) ∧
      Iso (perm π (kron S T)) (kron (perm π S) (perm π T)) ∧
      Iso (perm π (unit (F := F) 1)) (unit 1) ∧
      (Restricts T S → Restricts (perm π T) (perm π S))
