/- Adapted from PolMul/DegenerationFacts/Denominators.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMul.DegenerationFacts.Operations
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# Clearing rational-function denominators

This file implements the denominator-clearing calculation in the proof of
part (iv) of the degeneration facts.
-/

namespace OM.PolMul.DegenerationFacts

open AsymptoticSpectrumDuality Semicontinuity
open scoped BigOperators

universe u

variable {F : Type u} [Field F]

/-- After scaling a nonzero polynomial by the inverse of its trailing
coefficient, its first term is `X ^ natTrailingDegree`. -/
lemma factor_normalized_polynomial (p : Polynomial F) (hp : p ≠ 0) :
    ∃ E : Polynomial F,
      Polynomial.C p.trailingCoeff⁻¹ * p =
        Polynomial.X ^ p.natTrailingDegree +
          Polynomial.X ^ (p.natTrailingDegree + 1) * E := by
  have hc : p.trailingCoeff ≠ 0 :=
    Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hp
  have hdiv : Polynomial.X ^ (p.natTrailingDegree + 1) ∣
      Polynomial.C p.trailingCoeff⁻¹ * p - Polynomial.X ^ p.natTrailingDegree := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    have hdle : d ≤ p.natTrailingDegree := by omega
    by_cases hlt : d < p.natTrailingDegree
    · rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul,
        Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hlt]
      simp only [mul_zero, Polynomial.coeff_X_pow]
      simp [show d ≠ p.natTrailingDegree by omega]
    · have heq : d = p.natTrailingDegree := by omega
      subst d
      have hc' : p.coeff p.natTrailingDegree ≠ 0 := by
        exact Polynomial.coeff_natTrailingDegree_ne_zero.mpr hp
      simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul,
        Polynomial.trailingCoeff, Polynomial.coeff_X_pow, if_pos]
      rw [inv_mul_cancel₀ hc', sub_self]
  rcases hdiv with ⟨E, hE⟩
  refine ⟨E, ?_⟩
  rw [← hE]
  ring

/-- Clear one common polynomial denominator from all entries of the three
rational-function leg matrices, then normalize the lowest coefficient. -/
lemma arc_of_ratFunc_restricts {dT dS : Fin 3 → ℕ+} (T : T3 F dT) (S : T3 F dS)
    (h : Restricts (KTensor.baseChange (K := RatFunc F) T)
      (KTensor.baseChange (K := RatFunc F) S)) : Arc T S := by
  classical
  rcases h with ⟨A, hA⟩
  let entry : (Σ i : Fin 3, Fin (dT i) × Fin (dS i)) → RatFunc F :=
    fun z ↦ A z.1 z.2.1 z.2.2
  obtain ⟨D, hD⟩ :=
    IsLocalization.exist_integer_multiples_of_finite
      (M := nonZeroDivisors (Polynomial F)) entry
  let B : ∀ i : Fin 3, Matrix (Fin (dT i)) (Fin (dS i)) (Polynomial F) :=
    fun i x y ↦ (hD ⟨i, (x, y)⟩).choose
  have hB (i : Fin 3) (x : Fin (dT i)) (y : Fin (dS i)) :
      algebraMap (Polynomial F) (RatFunc F) (B i x y) =
        algebraMap (Polynomial F) (RatFunc F) (D : Polynomial F) * A i x y := by
    change algebraMap (Polynomial F) (RatFunc F)
        ((hD ⟨i, (x, y)⟩).choose) = _
    rw [(hD ⟨i, (x, y)⟩).choose_spec]
    simp only [Algebra.smul_def]
    rfl
  let p : Polynomial F := (D : Polynomial F) ^ 3
  have hp : p ≠ 0 := by
    apply pow_ne_zero
    exact nonZeroDivisors.ne_zero D.property
  have hclear (idx : ∀ i : Fin 3, Fin (dT i)) :
      action B (constTensor S) idx = p * Polynomial.C (T idx) := by
    apply RatFunc.algebraMap_injective
    rw [← map_action]
    calc
      action (fun i x y ↦ algebraMap (Polynomial F) (RatFunc F) (B i x y))
          (fun j ↦ algebraMap (Polynomial F) (RatFunc F) (constTensor S j)) idx =
          action (fun i x y ↦
              algebraMap (Polynomial F) (RatFunc F) (D : Polynomial F) * A i x y)
            (KTensor.baseChange (K := RatFunc F) S) idx := by
        congr 1
        · funext i x y
          exact hB i x y
      _ = algebraMap (Polynomial F) (RatFunc F) (D : Polynomial F) ^ 3 *
            action A (KTensor.baseChange (K := RatFunc F) S) idx := by
        unfold action
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        simp only [Fin.prod_univ_three]
        ring
      _ = algebraMap (Polynomial F) (RatFunc F) (D : Polynomial F) ^ 3 *
            algebraMap F (RatFunc F) (T idx) := by
        rw [show action A (KTensor.baseChange (K := RatFunc F) S) idx =
            KTensor.baseChange (K := RatFunc F) T idx by
          exact (hA idx).symm]
        rfl
      _ = algebraMap (Polynomial F) (RatFunc F)
            (p * Polynomial.C (T idx)) := by
        simp [p, map_mul, map_pow, RatFunc.algebraMap_C]
  rcases factor_normalized_polynomial p hp with ⟨E, hE⟩
  refine ⟨p.natTrailingDegree,
    scaleFirst (Polynomial.C p.trailingCoeff⁻¹) B,
    (fun idx ↦ E * Polynomial.C (T idx)), ?_⟩
  intro idx
  rw [action_scaleFirst, hclear, ← mul_assoc, hE, add_mul]
  ring

end OM.PolMul.DegenerationFacts
