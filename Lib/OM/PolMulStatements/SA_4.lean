/- Adapted from PLATFORM/Statements/SA.4.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMulStatements.DEF_1
import Lib.OM.PolMulStatements.DEF_4
import Lib.OM.PolMulStatements.DEF_7
import Lib.OM.PolMulStatements.DEF_8
import Lib.OM.PolMulStatements.DEF_11
import Lib.OM.PolMulStatements.DEF_14
import Lib.OM.PolMulStatements.DEF_22

open OM.PolMulDef

universe u

def OM_S_SA_4 : Prop :=
  ∀ (F : Type u) [Field F] {d : Fin 3 → ℕ+}
    (S : T3 F d) (s t : ℕ+),
      AsympRestricts
        (symm (kron S (matMul 1 1 (s + t))))
        (symm
          (pdsum
            (kron S (matMul 1 1 s))
            (kron (swap23 S) (matMul 1 1 t))
            (by
              change d 0 * 1 = d ((Equiv.swap 1 2).symm 0) * 1
              rw [Equiv.symm_swap,
                Equiv.swap_apply_of_ne_of_ne (by decide +kernel) (by decide +kernel)])))
