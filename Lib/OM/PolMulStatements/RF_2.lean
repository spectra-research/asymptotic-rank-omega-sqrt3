/- Adapted from PLATFORM/Statements/RF.2.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMulStatements.DEF_1
import Lib.OM.PolMulStatements.DEF_3
import Lib.OM.PolMulStatements.DEF_15

open OM.PolMulDef
open Semicontinuity

universe u

def OM_S_RF_2 : Prop :=
  ∀ (F : Type u) [Field F] {d : Fin 3 → ℕ+} (T : T3 F d),
    (OM.PolMulDef.tensorRank T = 0 ↔ T = 0) ∧
    ∀ r : ℕ+, OM.PolMulDef.tensorRank T ≤ (r : ℕ) ↔ Restricts T (unit r)
