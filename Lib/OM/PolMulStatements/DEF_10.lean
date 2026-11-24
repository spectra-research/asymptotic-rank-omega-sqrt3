/- Adapted from PLATFORM/Statements/DEF.10.lean of an earlier formalisation
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

/-- Permute tensor legs so that leg `i` of `T` becomes leg `π i` of the result.
Thus the output format is `d ∘ π.symm`.  This reuses
`Semicontinuity.KTensor.legReindex` with `π.symm`. -/
def perm (π : Equiv.Perm (Fin 3)) {d : Fin 3 → ℕ+} (T : T3 F d) :
    T3 F (d ∘ π.symm) :=
  KTensor.legReindex π.symm T

end OM.PolMulDef
