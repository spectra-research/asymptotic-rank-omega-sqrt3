/- Adapted from PLATFORM/Statements/DEF.2.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Amanov, van den Berg and Zuiddam (2026),
   “Multiplying matrices via polynomials: exposition and barriers”.
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMulStatements.DEF_1

namespace OM.PolMulDef

open AsymptoticSpectrumDuality
open Semicontinuity
open scoped BigOperators

universe u

variable {F : Type u} [Field F]

/-- The three-leg format `(n₁,n₂,n₃)`. -/
def fmt (n₁ n₂ n₃ : ℕ+) : Fin 3 → ℕ+
  | 0 => n₁
  | 1 => n₂
  | 2 => n₃

end OM.PolMulDef
