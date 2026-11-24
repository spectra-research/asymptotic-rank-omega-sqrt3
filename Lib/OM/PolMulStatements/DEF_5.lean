/- Adapted from PLATFORM/Statements/DEF.5.lean of an earlier formalisation
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

/-- The polynomial multiplication tensor `𝖯_{a,b}`: its `(i,j,l)` entry is
`1` iff the zero-based indices satisfy `l = i+j`. -/
def polmul (a b : ℕ+) : T3 F (fmt a b (a + b - 1)) :=
  fun idx => if (idx 2).val = (idx 0).val + (idx 1).val then 1 else 0

end OM.PolMulDef
