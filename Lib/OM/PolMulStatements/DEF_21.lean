/- Adapted from PLATFORM/Statements/DEF.21.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Amanov, van den Berg and Zuiddam (2026),
   “Multiplying matrices via polynomials: exposition and barriers”.
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMulStatements.DEF_19

namespace OM.PolMulDef

open AsymptoticSpectrumDuality
open Semicontinuity
open scoped BigOperators

universe u

variable {F : Type u} [Field F]

namespace Spectral

/-- The permuted spectral point `φ_π`, satisfying
`φ_π(T) = φ(π • T)` with the leg convention of `OM.PolMulDef.perm`. -/
noncomputable def perm (π : Equiv.Perm (Fin 3)) (φ : Spectral F) : Spectral F :=
  toAbstractSpectralPoint (F := F) (k := 3) (by norm_num)
    ((ofAbstractSpectralPoint (K := F) (k := 3) (by norm_num) φ).reindex π.symm)

end Spectral

end OM.PolMulDef
