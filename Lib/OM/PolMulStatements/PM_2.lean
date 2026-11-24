/- Adapted from PLATFORM/Statements/PM.2.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMulStatements.DEF_3
import Lib.OM.PolMulStatements.DEF_5
import Lib.OM.PolMulStatements.DEF_12

open OM.PolMulDef

universe u

def OM_S_PM_2 : Prop :=
  ∀ (F : Type u) [Field F] (n : ℕ+),
    Degen (unit (F := F) n) (polmul n n)
