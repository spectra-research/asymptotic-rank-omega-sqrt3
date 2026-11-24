/- Adapted from PLATFORM/Statements/DEF.4.lean of an earlier formalisation
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

/-- The matrix multiplication tensor `⟨n₁,n₂,n₃⟩`.  A coordinate decodes as
`(i,j),(j',k),(k',i')` using `finProdFinEquiv` and has value `1` exactly when
`i=i'`, `j=j'`, and `k=k'`. -/
def matMul (n₁ n₂ n₃ : ℕ+) :
    T3 F (fmt (n₁ * n₂) (n₂ * n₃) (n₃ * n₁)) := by
  intro idx
  let ij : Fin (n₁ : ℕ) × Fin (n₂ : ℕ) :=
    finProdFinEquiv.symm (by simpa [PNat.mul_coe] using! idx 0)
  let jk : Fin (n₂ : ℕ) × Fin (n₃ : ℕ) :=
    finProdFinEquiv.symm (by simpa [PNat.mul_coe] using! idx 1)
  let ki : Fin (n₃ : ℕ) × Fin (n₁ : ℕ) :=
    finProdFinEquiv.symm (by simpa [PNat.mul_coe] using! idx 2)
  exact if ij.2 = jk.1 ∧ jk.2 = ki.1 ∧ ki.2 = ij.1 then 1 else 0

end OM.PolMulDef
