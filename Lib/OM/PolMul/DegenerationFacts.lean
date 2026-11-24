/- Adapted from PolMul/DegenerationFacts.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Amanov, van den Berg and Zuiddam (2026),
   “Multiplying matrices via polynomials: exposition and barriers”.
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMul.DegenerationFacts.Denominators
import Lib.OM.PolMulStatements.DF_1
import Lib.OM.PolMulStatements.DF_2
import Lib.OM.PolMulStatements.DF_3
import Lib.OM.PolMulStatements.DF_4
import Lib.OM.PolMulStatements.DF_5

/-!
# Basic facts about polynomial degeneration

These are the five parts of the lemma on degeneration facts in Section 2.3.
-/

namespace OM.PolMul.DegenerationFacts

open AsymptoticSpectrumDuality
open Semicontinuity
open scoped BigOperators

universe u

/-- Part (i), using exactly the paper's constant-matrix,
`q = d = 0` argument. -/
theorem proof_DF_1 : OM_S_DF_1 := by
  intro F _ dT dS T S h
  rcases h with ⟨A, hA⟩
  apply degen_of_arc
  refine ⟨0, (fun i x y ↦ Polynomial.C (A i x y)), (fun _ ↦ 0), ?_⟩
  intro idx
  change (∑ sidx, (∏ i : Fin 3, Polynomial.C (A i (idx i) (sidx i))) *
      Polynomial.C (S sidx)) = _
  calc
    _ = ∑ sidx, Polynomial.C ((∏ i : Fin 3, A i (idx i) (sidx i)) * S sidx) := by
      apply Finset.sum_congr rfl
      intro sidx _
      rw [map_mul, map_prod]
    _ = Polynomial.C (∑ sidx, (∏ i : Fin 3, A i (idx i) (sidx i)) * S sidx) := by
      rw [map_sum]
    _ = Polynomial.C (T idx) := congrArg Polynomial.C (hA idx).symm
    _ = _ := by simp

/-- Part (ii).  This follows Strassen's parameter-power
composition: replace the inner parameter by its `(q+1)`-st power, then compose
the three pairs of polynomial matrices. -/
theorem proof_DF_2 : OM_S_DF_2 := by
  intro F _ d₁ d₂ d₃ T S U hTS hSU
  exact degen_of_arc ((arc_of_degen hTS).trans (arc_of_degen hSU))

/-- Part (iii).  This follows the paper's block-diagonal
direct-sum maps and Kronecker products of the three pairs of polynomial maps. -/
theorem proof_DF_3 : OM_S_DF_3 := by
  intro F _ dT₁ dS₁ dT₂ dS₂ T₁ S₁ T₂ S₂ h₁ h₂
  constructor
  · exact degen_of_arc ((arc_of_degen h₁).dsum (arc_of_degen h₂))
  · exact degen_of_arc ((arc_of_degen h₁).kron (arc_of_degen h₂))

/-- Part (iv), following the paper: clear a common
polynomial denominator from the rational-function matrices, then take and
normalize the lowest nonzero coefficient. -/
theorem proof_DF_4 : OM_S_DF_4 := by
  intro F _ dT dS T S h
  exact degen_of_arc (arc_of_ratFunc_restricts T S h)

/-- Part (v), directly permuting the three polynomial
matrix families as in the paper. -/
theorem proof_DF_5 : OM_S_DF_5 := by
  intro F _ π dT dS T S h
  exact degen_of_arc ((arc_of_degen h).perm π)

end OM.PolMul.DegenerationFacts

