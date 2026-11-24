/- Adapted from PLATFORM/Statements/DEF.3.lean of an earlier formalisation
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

/-- The unit tensor `⟨n⟩`, with value `1` exactly on the diagonal. -/
def unit (n : ℕ+) : T3 F (fmt n n n) :=
  fun idx => if ∀ i j : Fin 3, (idx i).val = (idx j).val then 1 else 0

-- NOTE: `Semicontinuity.unitTensor` has the same entries, but its constant
-- format `fun _ => n` is not definitionally `fmt n n n`; this definition keeps
-- the requested format without introducing a format-cast theorem.

end OM.PolMulDef
