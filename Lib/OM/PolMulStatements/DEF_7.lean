/- Adapted from PLATFORM/Statements/DEF.7.lean of an earlier formalisation
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

/-- Tensor (Kronecker) product with corresponding legs grouped.  This is `Semicontinuity.kroneckerTensor`. -/
noncomputable def kron {dT dS : Fin 3 → ℕ+} (T : T3 F dT) (S : T3 F dS) :
    T3 F (fun i => dT i * dS i) :=
  kroneckerTensor T S

end OM.PolMulDef
