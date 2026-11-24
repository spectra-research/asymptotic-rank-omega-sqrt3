/- Adapted from PLATFORM/Statements/DEF.23.lean of an earlier formalisation
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

/-- The direct sum of a nonempty `Fin m`-indexed family, block-diagonal in all
three legs.  `finSigmaFinEquiv` gives the consecutive-block encodings. -/
noncomputable def dsumFamily {m : ℕ} (d : Fin m → Fin 3 → ℕ+) [NeZero m]
    (T : ∀ i, T3 F (d i)) :
    T3 F (fun j => ⟨∑ i : Fin m, (d i j : ℕ), by
      exact Finset.sum_pos (fun i _ => (d i j).pos) Finset.univ_nonempty⟩) := by
  classical
  intro idx
  let block : ∀ j : Fin 3, (i : Fin m) × Fin (d i j : ℕ) :=
    fun j => finSigmaFinEquiv.symm (idx j)
  if h : ∀ j, (block j).1 = (block 0).1 then
    exact T (block 0).1 (fun j => Fin.cast (by rw [h j]) (block j).2)
  else
    exact 0

end OM.PolMulDef
