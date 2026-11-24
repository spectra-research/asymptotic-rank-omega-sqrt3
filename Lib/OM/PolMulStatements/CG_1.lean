/- Adapted from PLATFORM/Statements/CG.1.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMulStatements.DEF_5
import Lib.OM.PolMulStatements.DEF_8
import Lib.OM.PolMulStatements.DEF_13

open OM.PolMulDef

universe u

def OM_S_CG_1 : Prop :=
  ∀ (F : Type u) [Field F] (a b : ℕ+), 2 ≤ b →
    Degen23
      (pdsum (polmul (F := F) a (b + 1)) (polmul a (b - 1)) rfl)
      (pdsum (polmul a b) (polmul a b) rfl) rfl
