/- Adapted from PLATFORM/Statements/DF.2.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMulStatements.DEF_1
import Lib.OM.PolMulStatements.DEF_12

open OM.PolMulDef

universe u

def OM_S_DF_2 : Prop :=
  ∀ (F : Type u) [Field F] {d₁ d₂ d₃ : Fin 3 → ℕ+}
    (T : T3 F d₁) (S : T3 F d₂) (U : T3 F d₃),
      Degen T S → Degen S U → Degen T U
