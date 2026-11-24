/- Adapted from PLATFORM/Statements/DEF.12.lean of an earlier formalisation
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

/-- Polynomial degeneration: `T ⊴ S` when polynomial leg maps send `S` to
`X^q T + X^(q+1) T₁ + ... + X^(q+d) T_d`. -/
def Degen {dT dS : Fin 3 → ℕ+} (T : T3 F dT) (S : T3 F dS) : Prop :=
  ∃ q e : ℕ,
    ∃ A : ∀ i : Fin 3, Matrix (Fin (dT i)) (Fin (dS i)) (Polynomial F),
    ∃ R : Fin e → T3 F dT,
      ∀ idx : ∀ i : Fin 3, Fin (dT i),
        (∑ sidx : (∀ i : Fin 3, Fin (dS i)),
            (∏ i : Fin 3, A i (idx i) (sidx i)) * Polynomial.C (S sidx)) =
          Polynomial.X ^ q * Polynomial.C (T idx) +
            ∑ j : Fin e,
              Polynomial.X ^ (q + j.val + 1) * Polynomial.C (R j idx)

end OM.PolMulDef
