/- Adapted from PLATFORM/Statements/DEF.9.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Amanov, van den Berg and Zuiddam (2026),
   “Multiplying matrices via polynomials: exposition and barriers”.
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMulStatements.DEF_1
import Lib.OM.PolMulStatements.DEF_2

namespace OM.PolMulDef

open AsymptoticSpectrumDuality
open Semicontinuity
open scoped BigOperators

universe u

variable {F : Type u} [Field F]

/-- The partial direct sum of a nonempty `Fin m`-indexed family, with the first
leg shared as witnessed by `h`.  `finSigmaFinEquiv` gives the consecutive-block
encodings of the second and third legs. -/
noncomputable def pdsumFamily {m : ℕ} (d : Fin m → Fin 3 → ℕ+) (n : ℕ+)
    (h : ∀ i, d i 0 = n) [NeZero m] (T : ∀ i, T3 F (d i)) :
    T3 F (fmt n
      ⟨∑ i : Fin m, (d i 1 : ℕ), by
        exact Finset.sum_pos (fun i _ => (d i 1).pos) Finset.univ_nonempty⟩
      ⟨∑ i : Fin m, (d i 2 : ℕ), by
        exact Finset.sum_pos (fun i _ => (d i 2).pos) Finset.univ_nonempty⟩) := by
  classical
  intro idx
  let iv : (i : Fin m) × Fin (d i 1 : ℕ) := finSigmaFinEquiv.symm (idx 1)
  let iw : (i : Fin m) × Fin (d i 2 : ℕ) := finSigmaFinEquiv.symm (idx 2)
  if hi : iv.1 = iw.1 then
    exact T iv.1 (fun
      | 0 => Fin.cast (congrArg (fun x : ℕ+ => (x : ℕ)) (h iv.1).symm) (idx 0)
      | 1 => iv.2
      | 2 => Fin.cast (by rw [hi]) iw.2)
  else
    exact 0

end OM.PolMulDef
