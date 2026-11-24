/- Adapted from PLATFORM/Statements/DF.3.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMulStatements.DEF_1
import Lib.OM.PolMulStatements.DEF_6
import Lib.OM.PolMulStatements.DEF_7
import Lib.OM.PolMulStatements.DEF_12

open OM.PolMulDef

universe u

def OM_S_DF_3 : Prop :=
  ∀ (F : Type u) [Field F]
    {dT₁ dS₁ dT₂ dS₂ : Fin 3 → ℕ+}
    (T₁ : T3 F dT₁) (S₁ : T3 F dS₁)
    (T₂ : T3 F dT₂) (S₂ : T3 F dS₂),
      Degen T₁ S₁ → Degen T₂ S₂ →
        Degen (dsum T₁ T₂) (dsum S₁ S₂) ∧
        Degen (kron T₁ T₂) (kron S₁ S₂)
