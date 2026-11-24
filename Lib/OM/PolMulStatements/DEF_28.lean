/- Adapted from PLATFORM/Statements/DEF.28.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Amanov, van den Berg and Zuiddam (2026),
   “Multiplying matrices via polynomials: exposition and barriers”.
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMulStatements.DEF_1
import Lib.OM.PolMulStatements.DEF_2

namespace OM.PolMulDef

open AsymptoticSpectrumDuality
open Semicontinuity
open scoped BigOperators

universe u

variable {F : Type u} [Field F]

/-- Swap the second and third legs while retaining an explicit `fmt` output
format. -/
def swap23' {n v w : ℕ+} (T : T3 F (fmt n v w)) : T3 F (fmt n w v) :=
  fun idx => T (fun
    | 0 => idx 0
    | 1 => idx 2
    | 2 => idx 1)

end OM.PolMulDef
