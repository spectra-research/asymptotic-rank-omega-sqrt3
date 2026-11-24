/- Adapted from PLATFORM/Statements/DEF.14.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMulStatements.DEF_1

namespace OM.PolMulDef

open AsymptoticSpectrumDuality
open Semicontinuity
open scoped BigOperators

universe u

variable {F : Type u} [Field F]

noncomputable def AsympRestricts {dT dS : Fin 3 → ℕ+}
    (T : T3 F dT) (S : T3 F dS) : Prop :=
  AsympRel (tensorStrassenPreorder (F := F) (k := 3) (by norm_num))
    (TensorClass.mk ⟨dT, T⟩) (TensorClass.mk ⟨dS, S⟩)

end OM.PolMulDef
