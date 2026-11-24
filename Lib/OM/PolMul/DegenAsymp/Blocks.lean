/- Adapted from PolMul/DegenAsymp/Blocks.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMul.DegenAsymp.Coefficients
import Foundations.Tensors.Coordinates

namespace OM.PolMul.DegenAsymp

open Semicontinuity
open scoped BigOperators

universe u
variable {F : Type u} [Field F]

lemma unitTensor_diagonal_sum {k : ℕ} [NeZero k] {r : ℕ+} (f : (Fin k → Fin r) → F) :
    (∑ qIdx : Fin k → Fin r,
        f qIdx * unitTensor F (k := k) r qIdx)
      = ∑ q : Fin r, f (fun _ : Fin k => q) := by
  classical
  simp only [unitTensor]
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  refine (Finset.sum_bij
    (t := (Finset.univ : Finset (Fin r)))
    (f := f)
    (g := fun q : Fin r => f (fun _ : Fin k => q))
    (fun qIdx (_ : qIdx ∈ (Finset.univ.filter
        (fun qIdx : ∀ i : Fin k, Fin r => ∀ i j : Fin k, qIdx i = qIdx j))) =>
      if hk : Nonempty (Fin k) then qIdx (Classical.choice hk) else 0)
    ?_ ?_ ?_ ?_)
  · intro qIdx hqIdx
    simp
  · intro qIdx₁ hqIdx₁ qIdx₂ hqIdx₂ hq
    rw [Finset.mem_filter] at hqIdx₁ hqIdx₂
    obtain ⟨_, hdiag₁⟩ := hqIdx₁
    obtain ⟨_, hdiag₂⟩ := hqIdx₂
    funext i
    by_cases hk : Nonempty (Fin k)
    · calc
        qIdx₁ i = qIdx₁ (Classical.choice hk) := hdiag₁ i (Classical.choice hk)
        _ = qIdx₂ (Classical.choice hk) := by simpa [hk] using! hq
        _ = qIdx₂ i := (hdiag₂ i (Classical.choice hk)).symm
    · exact False.elim (hk ⟨i⟩)
  · intro q _
    refine ⟨fun _ : Fin k => q, ?_, ?_⟩
    · simp
    · have hk : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp (NeZero.pos k)
      simp [hk]
  · intro qIdx hqIdx
    rw [Finset.mem_filter] at hqIdx
    obtain ⟨_, hdiag⟩ := hqIdx
    congr 1
    funext i
    by_cases hk : Nonempty (Fin k)
    · simpa [hk] using! hdiag i (Classical.choice hk)
    · exact False.elim (hk ⟨i⟩)


/-- Explicit block matrices add `m` images of the same source tensor.  The
unit factor forces the same block label on all three legs. -/
lemma sum_images_restricts {dT dS : Fin 3 → ℕ+} (S : T3 F dS) (m : ℕ+)
    (B : Fin m → ∀ i : Fin 3, Matrix (Fin (dT i)) (Fin (dS i)) F) :
    Restricts
      (fun idx => ∑ c : Fin m, ∑ g : ∀ i, Fin (dS i),
        (∏ i, B c i (idx i) (g i)) * S g)
      (kroneckerTensor (unitTensor F (k := 3) m) S) := by
  classical
  refine ⟨fun i a b => B (kronDecodeL b) i a (kronDecodeR b), ?_⟩
  intro idx
  let E := kronIndexEquiv (d₁ := fun _ : Fin 3 => m) (d₂ := dS)
  rw [← E.symm.sum_comp (fun g =>
    (∏ i, B (kronDecodeL (g i)) i (idx i) (kronDecodeR (g i))) *
      kroneckerTensor (unitTensor F (k := 3) m) S g)]
  rw [Fintype.sum_prod_type]
  have hdecode (c : Fin 3 → Fin m) (g : ∀ i, Fin (dS i)) :
      kronLeftIndex (E.symm (c, g)) = c ∧ kronRightIndex (E.symm (c, g)) = g := by
    exact Prod.mk.inj (E.apply_symm_apply (c, g))
  have hentry (c : Fin 3 → Fin m) (g : ∀ i, Fin (dS i)) :
      (∏ i, B (kronDecodeL (E.symm (c, g) i)) i (idx i)
        (kronDecodeR (E.symm (c, g) i))) *
        kroneckerTensor (unitTensor F (k := 3) m) S (E.symm (c, g)) =
      ((∏ i, B (c i) i (idx i) (g i)) * S g) * unitTensor F (k := 3) m c := by
    simp only [kroneckerTensor, kronDecodeL_eq_kronLeftIndex,
      kronDecodeR_eq_kronRightIndex, (hdecode c g).1, (hdecode c g).2]
    ring
  simp_rw [hentry, ← Finset.sum_mul]
  rw [unitTensor_diagonal_sum]

/-- A family of restrictions with a common target format can be added using
one diagonal copy of the source per summand. -/
lemma sum_restrictions {dT dS : Fin 3 → ℕ+} (S : T3 F dS) (m : ℕ+)
    (T : Fin m → T3 F dT) (h : ∀ c, Restricts (T c) S) :
    Restricts (∑ c, T c) (kroneckerTensor (unitTensor F (k := 3) m) S) := by
  classical
  choose B hB using h
  have heq : (∑ c, T c) = fun idx => ∑ c : Fin m, ∑ g : ∀ i, Fin (dS i),
      (∏ i, B c i (idx i) (g i)) * S g := by
    funext idx
    simp only [Finset.sum_apply, hB]
  rw [heq]
  exact sum_images_restricts S m B

/-- Extracting a polynomial contraction's coefficient costs at most `(q+1)²`
copies of the source; this holds over finite as well as infinite fields. -/
lemma coefficient_restricts {dT dS : Fin 3 → ℕ+} (S : T3 F dS) (q : ℕ)
    (A : ∀ i : Fin 3, Matrix (Fin (dT i)) (Fin (dS i)) (Polynomial F)) :
    Restricts
      (fun idx => (∑ g : ∀ i, Fin (dS i),
        (∏ i, A i (idx i) (g i)) * Polynomial.C (S g)).coeff q)
      (kroneckerTensor
        (unitTensor F (k := 3) ⟨(q+1)^2, pow_pos (Nat.succ_pos q) 2⟩) S) := by
  classical
  let m : ℕ+ := ⟨(q+1)^2, pow_pos (Nat.succ_pos q) 2⟩
  let B : Fin m → ∀ i : Fin 3, Matrix (Fin (dT i)) (Fin (dS i)) F :=
    fun c i a b => exactifyCoef 2 q i (finFunctionFinEquiv.symm c) (A i a b)
  have h := sum_images_restricts S m B
  convert! h using 1
  funext idx
  rw [Polynomial.finset_sum_coeff, Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Polynomial.coeff_mul_C, ← Finset.sum_mul]
  congr 1
  exact (exactifyCoef_sum_eq_coeff 2 q (fun i => A i (idx i) (g i))).symm

end OM.PolMul.DegenAsymp
