/- Adapted from PolMul/Superadditivity/Core.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMul.DegenerationFacts.Core
import Lib.OM.PolMul.SpectralFacts

/-!
# Spectral evaluation helpers for superadditivity

These lemmas bridge the project's concrete tensor constructors and isomorphism
predicate to the quotient-semiring API in the asymptotic-spectrum dependency.
-/

namespace OM.PolMul.Superadditivity

open AsymptoticSpectrumDuality
open Semicontinuity
open scoped BigOperators

universe u

variable {F : Type u} [Field F]

private lemma action_one {d : Fin 3 → ℕ+}
    (T : T3 F d) (idx : ∀ i, Fin (d i)) :
    DegenerationFacts.action (fun _ ↦ (1 : Matrix _ _ F)) T idx = T idx := by
  classical
  unfold DegenerationFacts.action
  rw [Finset.sum_eq_single idx]
  · simp
  · intro jdx _ hjdx
    have hex : ∃ i : Fin 3, idx i ≠ jdx i := by
      by_contra h
      push_neg at h
      exact hjdx (funext fun i ↦ (h i).symm)
    obtain ⟨i, hi⟩ := hex
    rw [show (∏ j : Fin 3, (1 : Matrix (Fin (d j)) (Fin (d j)) F)
        (idx j) (jdx j)) = 0 by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hi]]
    simp
  · simp

/-- The invertible-matrix notion of tensor isomorphism implies mutual
restriction, hence equality of restriction classes. -/
lemma restrictsEquiv_of_iso {dT dS : Fin 3 → ℕ+}
    {T : T3 F dT} {S : T3 F dS} (h : Iso T S) : T ∼ₜ S := by
  classical
  rcases h with ⟨A, B, hAB, hBA, hT⟩
  constructor
  · exact ⟨A, hT⟩
  · refine ⟨B, fun idx ↦ ?_⟩
    calc
      S idx = DegenerationFacts.action (fun _ ↦ (1 : Matrix _ _ F)) S idx :=
        (action_one S idx).symm
      _ = DegenerationFacts.action (fun i ↦ B i * A i) S idx := by
        congr 2
        funext i
        exact (hBA i).symm
      _ = DegenerationFacts.action B
          (fun j ↦ DegenerationFacts.action A S j) idx :=
        DegenerationFacts.action_comp B A S idx
      _ = DegenerationFacts.action B T idx := by
        congr 2
        funext j
        exact (hT j).symm

lemma eval_iso (φ : Spectral F) {dT dS : Fin 3 → ℕ+}
    {T : T3 F dT} {S : T3 F dS} (h : Iso T S) :
    Spectral.eval φ T = Spectral.eval φ S := by
  change AsymptoticSpectrum.eval _ (TensorClass.mk ⟨dT, T⟩) φ =
    AsymptoticSpectrum.eval _ (TensorClass.mk ⟨dS, S⟩) φ
  have hclass : (TensorClass.mk ⟨dT, T⟩ : TensorClass F 3) =
      TensorClass.mk ⟨dS, S⟩ :=
    TensorClass.mk_eq_of_equiv
      (x := ⟨dT, T⟩) (y := ⟨dS, S⟩)
      (restrictsEquiv_of_iso (T := T) (S := S) h)
  rw [hclass]

lemma eval_kron (φ : Spectral F) {dT dS : Fin 3 → ℕ+}
    (T : T3 F dT) (S : T3 F dS) :
    Spectral.eval φ (kron T S) = Spectral.eval φ T * Spectral.eval φ S := by
  change AsymptoticSpectrum.eval _ (TensorClass.mk ⟨_, kron T S⟩) φ = _
  rw [show TensorClass.mk ⟨_, kron T S⟩ =
      (TensorClass.mk ⟨dT, T⟩ : TensorClass F 3) * TensorClass.mk ⟨dS, S⟩ by rfl,
    AsymptoticSpectrum.eval_mul]
  rfl

lemma eval_dsum (φ : Spectral F) {dT dS : Fin 3 → ℕ+}
    (T : T3 F dT) (S : T3 F dS) :
    Spectral.eval φ (dsum T S) = Spectral.eval φ T + Spectral.eval φ S := by
  change AsymptoticSpectrum.eval _ (TensorClass.mk ⟨_, dsum T S⟩) φ = _
  rw [show TensorClass.mk ⟨_, dsum T S⟩ =
      (TensorClass.mk ⟨dT, T⟩ : TensorClass F 3) + TensorClass.mk ⟨dS, S⟩ by rfl]
  exact φ.map_add _ _

lemma eval_nonneg (φ : Spectral F) {d : Fin 3 → ℕ+} (T : T3 F d) :
    0 ≤ Spectral.eval φ T := by
  exact AsymptoticSpectrum.eval_nonneg (p :=
    tensorStrassenPreorder (F := F) (k := 3) (by norm_num)) φ (TensorClass.mk ⟨d, T⟩)

lemma eval_restricts (φ : Spectral F) {dT dS : Fin 3 → ℕ+}
    {T : T3 F dT} {S : T3 F dS} (h : Restricts T S) :
    Spectral.eval φ T ≤ Spectral.eval φ S := by
  exact AsymptoticSpectrum.eval_mono _ φ h

lemma eval_restrictsEquiv (φ : Spectral F) {dT dS : Fin 3 → ℕ+}
    {T : T3 F dT} {S : T3 F dS} (h : T ∼ₜ S) :
    Spectral.eval φ T = Spectral.eval φ S :=
  le_antisymm (eval_restricts φ h.1) (eval_restricts φ h.2)

end OM.PolMul.Superadditivity
