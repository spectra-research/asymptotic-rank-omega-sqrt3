/- Adapted from PLATFORM/Statements/DEF.8.lean of an earlier formalisation
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

/-- Partial direct sum with the first leg shared, as witnessed by `h`.  The
second and third legs use matching left or right blocks, and mixed blocks are
zero. -/
noncomputable def pdsum {dT dS : Fin 3 → ℕ+}
    (T : T3 F dT) (S : T3 F dS) (h : dT 0 = dS 0) :
    T3 F (fmt (dT 0) (dT 1 + dS 1) (dT 2 + dS 2)) := by
  classical
  intro idx
  by_cases hv : (idx 1).val < (dT 1 : ℕ)
  · by_cases hw : (idx 2).val < (dT 2 : ℕ)
    · exact T (fun
        | 0 => Fin.cast (by simp [fmt]) (idx 0)
        | 1 => ⟨(idx 1).val, hv⟩
        | 2 => ⟨(idx 2).val, hw⟩)
    · exact 0
  · by_cases hw : (dT 2 : ℕ) ≤ (idx 2).val
    · exact S (fun
        | 0 => Fin.cast (congrArg (fun x : ℕ+ => (x : ℕ)) h) (idx 0)
        | 1 => ⟨(idx 1).val - (dT 1 : ℕ), by
            have hi := (idx 1).isLt
            simp only [fmt] at hi ⊢
            have hcoe := PNat.add_coe (dT 1) (dS 1)
            omega⟩
        | 2 => ⟨(idx 2).val - (dT 2 : ℕ), by
            have hi := (idx 2).isLt
            simp only [fmt] at hi ⊢
            have hcoe := PNat.add_coe (dT 2) (dS 2)
            omega⟩)
    · exact 0

end OM.PolMulDef
