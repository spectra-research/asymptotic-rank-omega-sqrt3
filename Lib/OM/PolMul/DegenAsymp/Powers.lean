/- Adapted from PolMul/DegenAsymp/Powers.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMul.DegenAsymp.Blocks
import Lib.OM.PolMul.DegenerationFacts.Operations

/-! # Leading coefficients and tensor powers -/

namespace OM.PolMul.DegenAsymp

open Semicontinuity DegenerationFacts
open scoped BigOperators

universe u
variable {F : Type u} [Field F]

/-- Polynomial contraction of a tensor by three leg matrices. -/
noncomputable def contraction {dT dS : Fin 3 → ℕ+} (S : T3 F dS)
    (A : ∀ i : Fin 3, Matrix (Fin (dT i)) (Fin (dS i)) (Polynomial F))
    (idx : ∀ i, Fin (dT i)) : Polynomial F :=
  ∑ g : ∀ i, Fin (dS i), (∏ i, A i (idx i) (g i)) * Polynomial.C (S g)

/-- A degeneration with its leading order retained. Factoring out `X^q`
lets multiplication preserve the order without degree bounds on the errors. -/
def Leading {dT dS : Fin 3 → ℕ+} (T : T3 F dT) (S : T3 F dS) (q : ℕ) : Prop :=
  ∃ (A : ∀ i : Fin 3, Matrix (Fin (dT i)) (Fin (dS i)) (Polynomial F))
    (P : (∀ i, Fin (dT i)) → Polynomial F),
    (∀ idx, contraction S A idx = Polynomial.X ^ q * P idx) ∧
    (∀ idx, (P idx).coeff 0 = T idx)

lemma leading_of_degen {dT dS : Fin 3 → ℕ+} {T : T3 F dT} {S : T3 F dS}
    (h : Degen T S) : ∃ q, Leading T S q := by
  classical
  obtain ⟨q, e, A, R, hA⟩ := h
  refine ⟨q, A, (fun idx => Polynomial.C (T idx) +
    ∑ j : Fin e, Polynomial.X ^ (j.val + 1) * Polynomial.C (R j idx)), ?_, ?_⟩
  · intro idx
    rw [contraction, hA]
    simp only [mul_add, Finset.mul_sum, pow_add, mul_assoc]
  · intro idx
    simp [Polynomial.finset_sum_coeff, Polynomial.coeff_X_pow]

lemma Leading.kron {dT dS dU dV : Fin 3 → ℕ+}
    {T : T3 F dT} {S : T3 F dS} {U : T3 F dU} {V : T3 F dV} {q r : ℕ}
    (h : Leading T S q) (h' : Leading U V r) :
    Leading (kron T U) (OM.PolMul.kron S V) (q+r) := by
  classical
  obtain ⟨A, P, hA, hP⟩ := h
  obtain ⟨B, Q, hB, hQ⟩ := h'
  refine ⟨kronMatrix A B,
    (fun idx => P (kronLeftIndex idx) * Q (kronRightIndex idx)), ?_, ?_⟩
  · intro idx
    have hcontract : contraction (OM.PolMul.kron S V) (kronMatrix A B) idx =
        contraction S A (kronLeftIndex idx) * contraction V B (kronRightIndex idx) := by
      change action (kronMatrix A B) (constTensor (OM.PolMul.kron S V)) idx = _
      unfold constTensor OM.PolMul.kron kroneckerTensor
      simp only [map_mul]
      exact action_kronMatrix A B (constTensor S) (constTensor V) idx
    rw [hcontract]
    rw [hA, hB, pow_add]
    ring
  · intro idx
    simp [Polynomial.mul_coeff_zero, hP, hQ, OM.PolMul.kron, kroneckerTensor]

/-- The dependency's positive powers avoid any intermediate format casts.
Their tensor classes are the usual semiring powers. -/
lemma Leading.kronPowNat {dT dS : Fin 3 → ℕ+}
    {T : T3 F dT} {S : T3 F dS} {q : ℕ} (h : Leading T S q) (n : ℕ) :
    Leading (kronPowNat T n) (kronPowNat S n) (q * (n+1)) := by
  induction n with
  | zero => simpa [kronPowNat] using! h
  | succ n ih =>
    simpa only [kronPowNat, Nat.mul_succ, kron] using! ih.kron h

lemma Leading.restricts {dT dS : Fin 3 → ℕ+}
    {T : T3 F dT} {S : T3 F dS} {q : ℕ} (h : Leading T S q) :
    Restricts T (kroneckerTensor
      (unitTensor F (k := 3) ⟨(q+1)^2, pow_pos (Nat.succ_pos q) 2⟩) S) := by
  obtain ⟨A, P, hA, hP⟩ := h
  have heq : (fun idx => (contraction S A idx).coeff q) = T := by
    funext idx
    rw [hA]
    simpa using! (Polynomial.coeff_X_pow_mul (P idx) q 0).trans (hP idx)
  rw [← heq]
  exact coefficient_restricts S q A

/-- The project's cast-based powers represent the dependency's semiring
powers. The cast is a restriction equivalence, in both directions. -/
lemma mk_kronPow {d : Fin 3 → ℕ+} (T : T3 F d) (n : ℕ) :
    (TensorClass.mk ⟨_, kronPow T n⟩ : TensorClass F 3) =
      TensorClass.mk ⟨d, T⟩ ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, TensorClass.one_def]
    apply TensorClass.mk_eq_of_equiv
    have heq : kronPow T 0 = unitTensor F (k := 3) 1 := by
      simp [kronPow, unitTensor_one_eq]
    rw [heq]
    exact RestrictsEquiv.refl _
  | succ n ih =>
    rw [pow_succ, ← ih, TensorClass.mk_mul]
    apply TensorClass.mk_eq_of_equiv
    let heq : ∀ i, ((d i ^ (n+1) : ℕ+) : ℕ) = ((d i ^ n * d i : ℕ+) : ℕ) :=
      fun i => by simp [pow_succ]
    constructor
    · exact Restricts.of_eq_cast heq (fun _ => rfl)
    · refine Restricts.of_eq_cast (fun i => (heq i).symm) (fun idx => ?_)
      simp only [kronPow, kron, Fin.cast_refl, id_eq]

end OM.PolMul.DegenAsymp
