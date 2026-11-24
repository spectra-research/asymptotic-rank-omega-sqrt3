/- Adapted from PLATFORM/Statements/SP.3.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMulStatements.DEF_3
import Lib.OM.PolMulStatements.DEF_19
import Lib.OM.PolMulStatements.DEF_20

open OM.PolMulDef

universe u

def OM_S_SP_3 : Prop :=
  ∀ (F : Type u) [Field F] (φ : Spectral F),
    (∀ d : Fin 3 → ℕ+, Spectral.eval φ (0 : T3 F d) = 0) ∧
    ∀ n : ℕ+, Spectral.eval φ (unit n) = ((n : ℕ) : ℝ)
