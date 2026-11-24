/- Adapted from PLATFORM/Statements/DEF.24.lean of an earlier formalisation
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

/-- Isomorphism of tensors, the paper's `≅`: `T` is the image of `S` under
leg matrices `A i` that are invertible, with inverses `B i`, in the restriction convention of
`Semicontinuity.Restricts` (`T idx = ∑ sidx, (∏ i, A i (idx i) (sidx i)) * S sidx`). -/
def Iso {dT dS : Fin 3 → ℕ+} (T : T3 F dT) (S : T3 F dS) : Prop :=
  ∃ (A : ∀ i : Fin 3, Matrix (Fin (dT i)) (Fin (dS i)) F)
    (B : ∀ i : Fin 3, Matrix (Fin (dS i)) (Fin (dT i)) F),
    (∀ i, A i * B i = 1) ∧ (∀ i, B i * A i = 1) ∧
    ∀ idx : ∀ i : Fin 3, Fin (dT i),
      T idx = ∑ sidx : (∀ i : Fin 3, Fin (dS i)), (∏ i : Fin 3, A i (idx i) (sidx i)) * S sidx

end OM.PolMulDef
