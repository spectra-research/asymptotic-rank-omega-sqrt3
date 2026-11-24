/- Adapted from PLATFORM/Statements/MAIN.1.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMulStatements.DEF_16

open OM.PolMulDef

universe u

def OM_S_MAIN_1 : Prop :=
  ∀ (F : Type u) [Field F], omegaF F ≤ (9 : ℝ) / 4
