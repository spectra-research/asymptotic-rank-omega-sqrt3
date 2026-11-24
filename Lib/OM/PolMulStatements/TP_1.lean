/- Adapted from PLATFORM/Statements/TP.1.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMulStatements.DEF_2
import Lib.OM.PolMulStatements.DEF_5
import Lib.OM.PolMulStatements.DEF_9
import Lib.OM.PolMulStatements.DEF_13
import Lib.OM.PolMulStatements.DEF_28

open OM.PolMulDef

universe u

def OM_S_TP_1 : Prop :=
  ∀ (F : Type u) [Field F] (a b : ℕ+),
    Degen23
      (pdsumFamily (m := 3)
        (fun
          | 0 => fmt a b (a + b - 1)
          | 1 => fmt a (a + b - 1) b
          | 2 => fmt a b (a + b - 1)) a
        (fun | 0 => rfl | 1 => rfl | 2 => rfl)
        (fun
          | 0 => polmul (F := F) a b
          | 1 => swap23' (polmul a b)
          | 2 => polmul a b))
      (polmul a (3 * b + a - 1)) rfl
