/- Adapted from PLATFORM/Statements/DEF.19.lean of an earlier formalisation
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

/-- Strassen's asymptotic spectrum of three-tensor restriction classes. -/
noncomputable def Spectral (F : Type u) [Field F] : Type u :=
  AsymptoticSpectrum (tensorStrassenPreorder (F := F) (k := 3) (by norm_num))

end OM.PolMulDef
