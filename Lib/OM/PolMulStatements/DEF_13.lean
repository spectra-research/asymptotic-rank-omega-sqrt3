/- Adapted from PLATFORM/Statements/DEF.13.lean of an earlier formalisation
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

/-- Degeneration on the second and third legs: the first-leg polynomial matrix
is the identity transported along the shared-leg equality `h`. -/
def Degen23 {dT dS : Fin 3 → ℕ+}
    (T : T3 F dT) (S : T3 F dS) (h : dT 0 = dS 0) : Prop :=
  ∃ q e : ℕ,
    ∃ A : ∀ i : Fin 3,
      Matrix (Fin (dT i)) (Fin (dS i)) (Polynomial F),
    ∃ R : Fin e → T3 F dT,
      (∀ x y : Fin (dT 0),
        A 0 x (Fin.cast (congrArg (fun z : ℕ+ => (z : ℕ)) h) y) = if x = y then 1 else 0) ∧
      ∀ idx : ∀ i : Fin 3, Fin (dT i),
        (∑ sidx : (∀ i : Fin 3, Fin (dS i)),
            (∏ i : Fin 3, A i (idx i) (sidx i)) * Polynomial.C (S sidx)) =
          Polynomial.X ^ q * Polynomial.C (T idx) +
            ∑ j : Fin e,
              Polynomial.X ^ (q + j.val + 1) * Polynomial.C (R j idx)

end OM.PolMulDef
