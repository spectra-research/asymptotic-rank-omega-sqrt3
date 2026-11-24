/- Adapted from PLATFORM/Statements/PM.4.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMulStatements.DEF_1
import Lib.OM.PolMulStatements.DEF_5
import Lib.OM.PolMulStatements.DEF_7
import Lib.OM.PolMulStatements.DEF_9
import Lib.OM.PolMulStatements.DEF_12
import Lib.OM.PolMulStatements.DEF_23

open OM.PolMulDef

universe u

def OM_S_PM_4 : Prop :=
  ∀ (F : Type u) [Field F] (m q : ℕ+)
    (d : Fin m → Fin 3 → ℕ+) (n : ℕ+)
    (h : ∀ i, d i 0 = n) (T : ∀ i, T3 F (d i)),
      Degen
        (kron (dsumFamily d T) (polmul 1 q))
        (kron (pdsumFamily d n h T) (polmul m q))
