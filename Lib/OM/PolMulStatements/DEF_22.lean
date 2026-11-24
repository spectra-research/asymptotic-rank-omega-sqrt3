/- Adapted from PLATFORM/Statements/DEF.22.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Amanov, van den Berg and Zuiddam (2026),
   “Multiplying matrices via polynomials: exposition and barriers”.
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMulStatements.DEF_1
import Lib.OM.PolMulStatements.DEF_10

namespace OM.PolMulDef

open AsymptoticSpectrumDuality
open Semicontinuity
open scoped BigOperators

universe u

variable {F : Type u} [Field F]

/-- Symmetrisation: the tensor product of all six leg permutations of `T`.
Each output-leg coordinate is decoded into its six factors in the canonical
`Fintype.equivFin` order (used in Section 4). -/
-- NOTE: the dependency has only binary `kroneckerTensor`; this heterogeneous
-- six-fold product is defined entrywise so its format is the pointwise product.
noncomputable def symm {d : Fin 3 → ℕ+} (T : T3 F d) :
    T3 F (fun i => ∏ π : Equiv.Perm (Fin 3), d (π.symm i)) := by
  classical
  intro idx
  let split : ∀ i : Fin 3, ∀ π : Equiv.Perm (Fin 3), Fin (d (π.symm i)) :=
    fun i =>
      (Fintype.equivFin (∀ π : Equiv.Perm (Fin 3), Fin (d (π.symm i)))).symm
        (Fin.cast (by
          rw [Fintype.card_pi]
          simpa only [Fintype.card_fin] using!
            (map_prod PNat.coeMonoidHom (fun π : Equiv.Perm (Fin 3) => d (π.symm i))
              Finset.univ).symm) (idx i))
  exact ∏ π : Equiv.Perm (Fin 3), perm π T (fun i => split i π)

end OM.PolMulDef
