/- Adapted from PLATFORM/Statements/RF.1.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMulStatements.DEF_1
import Lib.OM.PolMulStatements.DEF_3

open OM.PolMulDef
open Semicontinuity

universe u

def OM_S_RF_1 : Prop :=
  ∀ (F : Type u) [Field F] {d : Fin 3 → ℕ+} (T : T3 F d),
    T ≠ 0 → Restricts (unit 1) T
