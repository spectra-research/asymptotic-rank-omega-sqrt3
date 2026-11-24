/- Adapted from PLATFORM/Statements/DF.4.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMulStatements.DEF_1
import Lib.OM.PolMulStatements.DEF_12
import Mathlib.FieldTheory.RatFunc.Basic

open OM.PolMulDef
open Semicontinuity

universe u


def OM_S_DF_4 : Prop :=
  ∀ (F : Type u) [Field F] {dT dS : Fin 3 → ℕ+}
    (T : T3 F dT) (S : T3 F dS),
      Restricts (KTensor.baseChange (K := RatFunc F) T)
        (KTensor.baseChange (K := RatFunc F) S) → Degen T S
