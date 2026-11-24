/- Adapted from PLATFORM/Statements/PR.1.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMulStatements.DEF_5
import Lib.OM.PolMulStatements.DEF_19
import Lib.OM.PolMulStatements.DEF_20

open OM.PolMulDef

universe u

def OM_S_PR_1 : Prop :=
  ∀ (F : Type u) [Field F] (φ : Spectral F) (a b : ℕ+),
    (((min a b : ℕ+) : ℕ) : ℝ) ≤ Spectral.eval φ (polmul a b) ∧
    Spectral.eval φ (polmul a b) ≤ (((a + b - 1 : ℕ+) : ℕ) : ℝ) ∧
    (∀ a' : ℕ+, a ≤ a' →
      Spectral.eval φ (polmul a b) ≤ Spectral.eval φ (polmul a' b)) ∧
    (∀ b' : ℕ+, b ≤ b' →
      Spectral.eval φ (polmul a b) ≤ Spectral.eval φ (polmul a b'))
