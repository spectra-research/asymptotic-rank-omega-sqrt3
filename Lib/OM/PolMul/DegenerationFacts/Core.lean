/- Adapted from PolMul/DegenerationFacts/Core.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMul.Defs
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.RingTheory.Localization.Integer

/-!
# Algebraic core for the elementary degeneration facts

The paper defines a degeneration by a polynomial family whose first nonzero
coefficient is the target tensor.  This file packages that calculation as
`Arc`, and supplies the finite coefficient expansion which converts an arc
back to the definition `Degen`.
-/

namespace OM.PolMul.DegenerationFacts

open AsymptoticSpectrumDuality
open Semicontinuity
open scoped BigOperators

universe u v

variable {F : Type u} [Field F]

/-- Apply leg matrices over a commutative semiring to an array. -/
noncomputable def action {R : Type v} [CommSemiring R]
    {dT dS : Fin 3 → ℕ+}
    (A : ∀ i : Fin 3, Matrix (Fin (dT i)) (Fin (dS i)) R)
    (S : (∀ i : Fin 3, Fin (dS i)) → R)
    (idx : ∀ i : Fin 3, Fin (dT i)) : R :=
  ∑ sidx, (∏ i : Fin 3, A i (idx i) (sidx i)) * S sidx

/-- The coefficientwise constant-polynomial copy of a tensor. -/
noncomputable def constTensor {d : Fin 3 → ℕ+} (T : T3 F d) :
    (∀ i : Fin 3, Fin (d i)) → Polynomial F :=
  fun idx ↦ Polynomial.C (T idx)

/-- An arc is the useful factored form of the polynomial degeneration equation. -/
def Arc {dT dS : Fin 3 → ℕ+} (T : T3 F dT) (S : T3 F dS) : Prop :=
  ∃ (q : ℕ)
    (A : ∀ i : Fin 3, Matrix (Fin (dT i)) (Fin (dS i)) (Polynomial F))
    (E : (∀ i : Fin 3, Fin (dT i)) → Polynomial F),
    ∀ idx, action A (constTensor S) idx =
      Polynomial.X ^ q * Polynomial.C (T idx) + Polynomial.X ^ (q + 1) * E idx

/-- The displayed finite-error definition immediately gives a factored arc. -/
lemma arc_of_degen {dT dS : Fin 3 → ℕ+} {T : T3 F dT} {S : T3 F dS}
    (h : Degen T S) : Arc T S := by
  rcases h with ⟨q, e, A, R, h⟩
  refine ⟨q, A, fun idx ↦ ∑ j : Fin e, Polynomial.X ^ j.val * Polynomial.C (R j idx), ?_⟩
  intro idx
  unfold action constTensor
  rw [h idx]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hexp : q + j.val + 1 = (q + 1) + j.val := by omega
  calc
    Polynomial.X ^ (q + j.val + 1) * Polynomial.C (R j idx) =
        Polynomial.X ^ ((q + 1) + j.val) * Polynomial.C (R j idx) := by rw [← hexp]
    _ = (Polynomial.X ^ (q + 1) * Polynomial.X ^ j.val) *
          Polynomial.C (R j idx) := by
      rw [pow_add]
    _ = Polynomial.X ^ (q + 1) *
          (Polynomial.X ^ j.val * Polynomial.C (R j idx)) := by ac_rfl

/-- A factored polynomial arc has a single uniform finite error length, since
the target format is finite. -/
lemma degen_of_arc {dT dS : Fin 3 → ℕ+} {T : T3 F dT} {S : T3 F dS}
    (h : Arc T S) : Degen T S := by
  classical
  rcases h with ⟨q, A, E, hE⟩
  let N : ℕ := Finset.univ.sup fun idx : (∀ i : Fin 3, Fin (dT i)) ↦ (E idx).natDegree
  let e : ℕ := N + 1
  refine ⟨q, e, A, fun j idx ↦ (E idx).coeff j.val, ?_⟩
  intro idx
  change action A (constTensor S) idx = _
  rw [hE idx]
  congr 1
  have hdeg : (E idx).natDegree < e := by
    apply Nat.lt_succ_of_le
    exact Finset.le_sup (f := fun x : (∀ i : Fin 3, Fin (dT i)) ↦ (E x).natDegree)
      (Finset.mem_univ idx)
  rw [(E idx).as_sum_range_C_mul_X_pow' hdeg]
  rw [← Fin.sum_univ_eq_sum_range]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hexp : q + j.val + 1 = (q + 1) + j.val := by omega
  calc
    Polynomial.X ^ (q + 1) *
          (Polynomial.C ((E idx).coeff j.val) * Polynomial.X ^ j.val) =
        (Polynomial.X ^ (q + 1) * Polynomial.X ^ j.val) *
          Polynomial.C ((E idx).coeff j.val) := by ac_rfl
    _ = Polynomial.X ^ ((q + 1) + j.val) * Polynomial.C ((E idx).coeff j.val) := by
      exact congrArg (fun z : Polynomial F ↦ z * Polynomial.C ((E idx).coeff j.val))
        (pow_add Polynomial.X (q + 1) j.val).symm
    _ = Polynomial.X ^ (q + j.val + 1) * Polynomial.C ((E idx).coeff j.val) := by
      rw [hexp]

/-- The degeneration predicate is equivalent to the factored arc form. -/
lemma degen_iff_arc {dT dS : Fin 3 → ℕ+} {T : T3 F dT} {S : T3 F dS} :
    Degen T S ↔ Arc T S :=
  ⟨arc_of_degen, degen_of_arc⟩

section ActionAlgebra

variable {R : Type v} [CommSemiring R]

/-- Applying two families of leg maps successively multiplies their matrices. -/
lemma action_comp {d₁ d₂ d₃ : Fin 3 → ℕ+}
    (A : ∀ i : Fin 3, Matrix (Fin (d₁ i)) (Fin (d₂ i)) R)
    (B : ∀ i : Fin 3, Matrix (Fin (d₂ i)) (Fin (d₃ i)) R)
    (U : (∀ i : Fin 3, Fin (d₃ i)) → R)
    (idx : ∀ i : Fin 3, Fin (d₁ i)) :
    action (fun i ↦ A i * B i) U idx = action A (fun j ↦ action B U j) idx := by
  classical
  symm
  unfold action
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro kdx _
  have hfactor : ∀ jdx : (∀ i : Fin 3, Fin (d₂ i)),
      (∏ i, A i (idx i) (jdx i)) *
          ((∏ i, B i (jdx i) (kdx i)) * U kdx) =
        (∏ i, A i (idx i) (jdx i) * B i (jdx i) (kdx i)) * U kdx := by
    intro jdx
    rw [Finset.prod_mul_distrib]
    ac_rfl
  simp_rw [hfactor]
  rw [← Finset.sum_mul]
  congr 1
  have hmulapply :
      (∏ i, (A i * B i) (idx i) (kdx i)) =
        ∏ i, ∑ m : Fin (d₂ i), A i (idx i) m * B i m (kdx i) := by
    refine Finset.prod_congr rfl ?_
    intro i _
    rw [Matrix.mul_apply]
  rw [hmulapply]
  rw [Finset.prod_univ_sum
    (t := fun _ : Fin 3 ↦ (Finset.univ : Finset (Fin (d₂ _))))
    (f := fun (i : Fin 3) (m : Fin (d₂ i)) ↦ A i (idx i) m * B i m (kdx i))]
  rw [show Fintype.piFinset (fun i : Fin 3 ↦ (Finset.univ : Finset (Fin (d₂ i)))) =
      (Finset.univ : Finset (∀ i : Fin 3, Fin (d₂ i))) from by
    ext
    simp]

/-- `action` is additive in its tensor argument. -/
lemma action_add {dT dS : Fin 3 → ℕ+}
    (A : ∀ i : Fin 3, Matrix (Fin (dT i)) (Fin (dS i)) R)
    (S T : (∀ i : Fin 3, Fin (dS i)) → R) (idx : ∀ i : Fin 3, Fin (dT i)) :
    action A (fun j ↦ S j + T j) idx = action A S idx + action A T idx := by
  unfold action
  simp only [mul_add, Finset.sum_add_distrib]

/-- Scalars can be pulled through `action`. -/
lemma action_smul {dT dS : Fin 3 → ℕ+}
    (A : ∀ i : Fin 3, Matrix (Fin (dT i)) (Fin (dS i)) R)
    (c : R) (S : (∀ i : Fin 3, Fin (dS i)) → R)
    (idx : ∀ i : Fin 3, Fin (dT i)) :
    action A (fun j ↦ c * S j) idx = c * action A S idx := by
  unfold action
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A commutative-semiring homomorphism commutes with finite tensor action. -/
lemma map_action {Q : Type*} [CommSemiring Q] (f : R →+* Q)
    {dT dS : Fin 3 → ℕ+}
    (A : ∀ i : Fin 3, Matrix (Fin (dT i)) (Fin (dS i)) R)
    (S : (∀ i : Fin 3, Fin (dS i)) → R)
    (idx : ∀ i : Fin 3, Fin (dT i)) :
    action (fun i x y ↦ f (A i x y)) (fun j ↦ f (S j)) idx = f (action A S idx) := by
  unfold action
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul, map_prod]

/-- Reindexing the three legs only reindexes the corresponding matrices. -/
lemma action_reindex {dT dS : Fin 3 → ℕ+} (σ : Equiv.Perm (Fin 3))
    (A : ∀ i : Fin 3, Matrix (Fin (dT i)) (Fin (dS i)) R)
    (S : (∀ i : Fin 3, Fin (dS i)) → R)
    (idx : ∀ i : Fin 3, Fin (dT (σ i))) :
    action (fun i ↦ A (σ i))
        (fun j ↦ S (Equiv.piCongrLeft (fun i ↦ Fin (dS i : ℕ)) σ j)) idx =
      action A S (Equiv.piCongrLeft (fun i ↦ Fin (dT i : ℕ)) σ idx) := by
  classical
  unfold action
  rw [← Equiv.sum_comp (Equiv.piCongrLeft (fun i ↦ Fin (dS i : ℕ)) σ)
    (fun j ↦ (∏ i, A i
      ((Equiv.piCongrLeft (fun i ↦ Fin (dT i : ℕ)) σ idx) i) (j i)) * S j)]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  rw [← Equiv.prod_comp σ (fun i ↦ A i
    ((Equiv.piCongrLeft (fun i ↦ Fin (dT i : ℕ)) σ idx) i)
    ((Equiv.piCongrLeft (fun i ↦ Fin (dS i : ℕ)) σ j) i))]
  apply Finset.prod_congr rfl
  intro i _
  rw [Equiv.piCongrLeft_apply_apply, Equiv.piCongrLeft_apply_apply]

end ActionAlgebra

/-- Transitivity of arcs, with the inner parameter replaced by its `(q+1)`-st
power so that its error starts strictly after the outer leading term. -/
lemma Arc.trans {d₁ d₂ d₃ : Fin 3 → ℕ+}
    {T : T3 F d₁} {S : T3 F d₂} {U : T3 F d₃}
    (hTS : Arc T S) (hSU : Arc S U) : Arc T U := by
  classical
  rcases hTS with ⟨q, A, E₁, hA⟩
  rcases hSU with ⟨r, B, E₂, hB⟩
  let N : ℕ := q + 1
  let B' : ∀ i : Fin 3, Matrix (Fin (d₂ i)) (Fin (d₃ i)) (Polynomial F) :=
    fun i x y ↦ Polynomial.expand F N (B i x y)
  let C : ∀ i : Fin 3, Matrix (Fin (d₁ i)) (Fin (d₃ i)) (Polynomial F) :=
    fun i ↦ A i * B' i
  let Q : ℕ := r * N + q
  refine ⟨Q, C, fun idx ↦ E₁ idx + action A
      (fun j ↦ Polynomial.expand F N (E₂ j)) idx, ?_⟩
  intro idx
  have hB' (j : ∀ i : Fin 3, Fin (d₂ i)) :
      action B' (constTensor U) j =
        Polynomial.X ^ (r * N) * Polynomial.C (S j) +
          Polynomial.X ^ ((r + 1) * N) * Polynomial.expand F N (E₂ j) := by
    calc
      action B' (constTensor U) j =
          Polynomial.expand F N (action B (constTensor U) j) := by
        simpa [B', constTensor] using!
          (map_action (Polynomial.expand F N).toRingHom B (constTensor U) j)
      _ = Polynomial.expand F N
          (Polynomial.X ^ r * Polynomial.C (S j) + Polynomial.X ^ (r + 1) * E₂ j) := by
        rw [hB j]
      _ = Polynomial.X ^ (r * N) * Polynomial.C (S j) +
          Polynomial.X ^ ((r + 1) * N) * Polynomial.expand F N (E₂ j) := by
        simp only [map_add, map_mul, map_pow, Polynomial.expand_X, Polynomial.expand_C]
        rw [pow_mul, pow_mul]
        congr 2
        · exact (pow_mul Polynomial.X N r).symm.trans <|
            (congrArg (fun n : ℕ ↦ Polynomial.X ^ n) (Nat.mul_comm N r)).trans
              (pow_mul Polynomial.X r N)
        · exact (pow_mul Polynomial.X N (r + 1)).symm.trans <|
            (congrArg (fun n : ℕ ↦ Polynomial.X ^ n) (Nat.mul_comm N (r + 1))).trans
              (pow_mul Polynomial.X (r + 1) N)
  calc
    action C (constTensor U) idx = action A (fun j ↦ action B' (constTensor U) j) idx := by
      exact action_comp A B' (constTensor U) idx
    _ = action A (fun j ↦
          Polynomial.X ^ (r * N) * Polynomial.C (S j) +
            Polynomial.X ^ ((r + 1) * N) * Polynomial.expand F N (E₂ j)) idx := by
      congr 2
      funext j
      exact hB' j
    _ = Polynomial.X ^ (r * N) * action A (constTensor S) idx +
          Polynomial.X ^ ((r + 1) * N) *
            action A (fun j ↦ Polynomial.expand F N (E₂ j)) idx := by
      rw [action_add, action_smul, action_smul]
      rfl
    _ = Polynomial.X ^ (r * N) *
          (Polynomial.X ^ q * Polynomial.C (T idx) + Polynomial.X ^ (q + 1) * E₁ idx) +
          Polynomial.X ^ ((r + 1) * N) *
            action A (fun j ↦ Polynomial.expand F N (E₂ j)) idx := by
      rw [hA idx]
    _ = Polynomial.X ^ Q * Polynomial.C (T idx) + Polynomial.X ^ (Q + 1) *
          (E₁ idx + action A (fun j ↦ Polynomial.expand F N (E₂ j)) idx) := by
      have hmain : r * N + q = Q := rfl
      have herr₁ : r * N + (q + 1) = Q + 1 := by simp only [Q, N]; omega
      have herr₂ : (r + 1) * N = Q + 1 := by
        simp only [Q, N, Nat.add_mul, one_mul]
        omega
      rw [mul_add]
      rw [← mul_assoc, ← mul_assoc]
      rw [← pow_add, ← pow_add, hmain, herr₁, herr₂]
      ring

/-- An arc is preserved when its three legs are permuted. -/
lemma Arc.perm {dT dS : Fin 3 → ℕ+} {T : T3 F dT} {S : T3 F dS}
    (π : Equiv.Perm (Fin 3)) (h : Arc T S) : Arc (OM.PolMul.perm π T) (OM.PolMul.perm π S) := by
  rcases h with ⟨q, A, E, hA⟩
  let σ := π.symm
  refine ⟨q, (fun i ↦ A (σ i)),
    (fun idx ↦ E (Equiv.piCongrLeft (fun i ↦ Fin (dT i : ℕ)) σ idx)), ?_⟩
  intro idx
  rw [show action (fun i ↦ A (σ i)) (constTensor (OM.PolMul.perm π S)) idx =
      action A (constTensor S)
        (Equiv.piCongrLeft (fun i ↦ Fin (dT i : ℕ)) σ idx) by
    simpa [σ, OM.PolMul.perm, KTensor.legReindex, constTensor] using!
      action_reindex σ A (constTensor S) idx]
  rw [hA]
  rfl

end OM.PolMul.DegenerationFacts
