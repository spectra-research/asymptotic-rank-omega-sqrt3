/- Adapted from PLATFORM/Statements/MAIN.2.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMulStatements.DEF_4
import Lib.OM.PolMulStatements.DEF_15

open OM.PolMulDef

universe u

def OM_S_MAIN_2 : Prop :=
  ∀ (F : Type u) [Field F] (ε : ℝ), 0 < ε →
    ∃ C : ℝ, ∀ n : ℕ+,
      (tensorRank (matMul (F := F) n n n) : ℝ) ≤
        C * (((n : ℕ) : ℝ) ^ ((9 : ℝ) / 4 + ε))
