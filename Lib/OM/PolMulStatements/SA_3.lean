/- Adapted from PLATFORM/Statements/SA.3.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMulStatements.DEF_16

open OM.PolMulDef

universe u

def OM_S_SA_3 : Prop :=
  ∀ (F : Type u) [Field F] (q : ℕ), 1 ≤ q →
    (((2 * q : ℕ) : ℝ) ^ omegaF F) ≤
      (((q + 1 : ℕ) : ℝ) ^ (3 : ℝ))
