/- Adapted from PLATFORM/Statements/DEF.1.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Amanov, van den Berg and Zuiddam (2026),
   “Multiplying matrices via polynomials: exposition and barriers”.
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Foundations.Tensors.Semicontinuity.SpectralPointExtension
import Foundations.Tensors.Semicontinuity.TensorRank
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.Polynomial.Basic

namespace OM.PolMulDef

open AsymptoticSpectrumDuality
open Semicontinuity
open scoped BigOperators

universe u

variable {F : Type u} [Field F]

/-- Three-tensors over `F` in positive format `d`. -/
abbrev T3 (F : Type u) [Field F] (d : Fin 3 → ℕ+) := KTensor F d

end OM.PolMulDef
