/- Adapted from PLATFORM/Statements/DEF.20.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Amanov, van den Berg and Zuiddam (2026),
   “Multiplying matrices via polynomials: exposition and barriers”.
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMulStatements.DEF_1
import Lib.OM.PolMulStatements.DEF_19

namespace OM.PolMulDef

open AsymptoticSpectrumDuality
open Semicontinuity
open scoped BigOperators

universe u

variable {F : Type u} [Field F]

namespace Spectral

/-- Evaluate a spectral point on a tensor through `TensorClass.mk`. -/
noncomputable def eval (φ : Spectral F) {d : Fin 3 → ℕ+} (T : T3 F d) : ℝ :=
  AsymptoticSpectrum.eval
    (tensorStrassenPreorder (F := F) (k := 3) (by norm_num))
    (TensorClass.mk ⟨d, T⟩) φ

end Spectral

end OM.PolMulDef
