/- Adapted from PLATFORM/Statements/RF.5.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMulStatements.DEF_4
import Lib.OM.PolMulStatements.DEF_7
import Lib.OM.PolMulStatements.DEF_10
import Lib.OM.PolMulStatements.DEF_22
import Lib.OM.PolMulStatements.DEF_24

open OM.PolMulDef

universe u

def OM_S_RF_5 : Prop :=
  ∀ (F : Type u) [Field F] (n₁ n₂ n₃ : ℕ+),
    let N := n₁ * n₂ * n₃
    Iso (perm (finRotate 3) (matMul (F := F) n₁ n₂ n₃))
        (matMul n₃ n₁ n₂) ∧
    Iso (perm (finRotate 3)⁻¹ (matMul (F := F) n₁ n₂ n₃))
        (matMul n₂ n₃ n₁) ∧
    Iso (perm (Equiv.swap 0 1) (matMul (F := F) n₁ n₂ n₃))
        (matMul n₃ n₂ n₁) ∧
    Iso (perm (Equiv.swap 0 2) (matMul (F := F) n₁ n₂ n₃))
        (matMul n₁ n₃ n₂) ∧
    Iso (perm (Equiv.swap 1 2) (matMul (F := F) n₁ n₂ n₃))
        (matMul n₂ n₁ n₃) ∧
    Iso (symm (matMul (F := F) n₁ n₂ n₃))
        (kron (matMul N N N) (matMul N N N))
