/- Adapted from PLATFORM/Statements/RF.3.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMulStatements.DEF_4
import Lib.OM.PolMulStatements.DEF_7
import Lib.OM.PolMulStatements.DEF_24

open OM.PolMulDef

universe u

def OM_S_RF_3 : Prop :=
  ∀ (F : Type u) [Field F] (n₁ n₂ n₃ m₁ m₂ m₃ : ℕ+),
    Iso (kron (matMul (F := F) n₁ n₂ n₃) (matMul m₁ m₂ m₃))
      (matMul (n₁ * m₁) (n₂ * m₂) (n₃ * m₃))
