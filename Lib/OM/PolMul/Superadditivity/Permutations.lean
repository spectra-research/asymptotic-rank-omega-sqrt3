/- Adapted from PolMul/Superadditivity/Permutations.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMul.Superadditivity.Binary
import Lib.OM.PolMul.RestrictionFacts

/-! # Spectral permutation identities for superadditivity -/

namespace OM.PolMul.Superadditivity

open AsymptoticSpectrumDuality Semicontinuity
open scoped BigOperators

universe u
variable {F : Type u} [Field F]

lemma eval_perm (φ : Spectral F) (π : Equiv.Perm (Fin 3))
    {d : Fin 3 → ℕ+} (T : T3 F d) :
    Spectral.eval (Spectral.perm π φ) T = Spectral.eval φ (perm π T) :=
  SpectralFacts.proof_SP_6 F π φ T

lemma perm_perm_iso (π σ : Equiv.Perm (Fin 3)) {d : Fin 3 → ℕ+} (T : T3 F d) :
    Iso (perm π (perm σ T)) (perm (π * σ) T) := by
  apply iso_of_coordinates _ _ (fun _ => Equiv.refl _)
  intro x
  simp only [perm, KTensor.legReindex]
  congr 1
  funext i
  apply Fin.ext
  simp only [piCongrLeft_val, Equiv.symm_symm, Equiv.Perm.coe_mul, Function.comp_apply, Equiv.refl_apply]

lemma eval_perm_perm (φ : Spectral F) (π σ : Equiv.Perm (Fin 3))
    {d : Fin 3 → ℕ+} (T : T3 F d) :
    Spectral.eval (Spectral.perm σ (Spectral.perm π φ)) T =
      Spectral.eval (Spectral.perm (π * σ) φ) T := by
  rw [eval_perm, eval_perm, eval_perm]
  exact eval_iso φ (perm_perm_iso π σ T)

lemma eval_swap_swap (φ : Spectral F) {d : Fin 3 → ℕ+} (T : T3 F d) :
    Spectral.eval (Spectral.perm (Equiv.swap 1 2) φ) (swap23 T) = Spectral.eval φ T := by
  rw [eval_perm]
  apply eval_restrictsEquiv
  exact ⟨by simpa [swap23, perm, Equiv.symm_swap] using!
      KTensor.legReindex_legReindex_restricts (Equiv.swap (1 : Fin 3) 2) T,
    by simpa [swap23, perm, Equiv.symm_swap] using!
      KTensor.restricts_legReindex_legReindex (Equiv.swap (1 : Fin 3) 2) T⟩

lemma eval_swap_matMul_11 (φ : Spectral F) (q : ℕ+) :
    Spectral.eval (Spectral.perm (Equiv.swap 1 2) φ) (matMul (F := F) 1 1 q) =
      Spectral.eval φ (matMul (F := F) 1 1 q) := by
  rw [eval_perm]
  exact eval_iso φ (RestrictionFacts.proof_RF_5 F 1 1 q).2.2.2.2.1

-- Comparing the two six-factor encodings needs additional definitional reduction.
set_option maxHeartbeats 300000 in
lemma eval_symm (φ : Spectral F) {d : Fin 3 → ℕ+} (T : T3 F d) :
    Spectral.eval φ (symm T) =
      ∏ π : Equiv.Perm (Fin 3), Spectral.eval (Spectral.perm π φ) T := by
  classical
  let E (i : Fin 3) : Fin (∏ π : Equiv.Perm (Fin 3), d (π.symm i) : ℕ+) ≃
      (∀ π : Equiv.Perm (Fin 3), Fin (d (π.symm i))) :=
    (finCongr (by
      rw [Fintype.card_pi]
      simpa only [Fintype.card_fin] using!
        (map_prod PNat.coeMonoidHom (fun π : Equiv.Perm (Fin 3) => d (π.symm i))
          Finset.univ).symm)).trans (Fintype.equivFin _).symm
  have hi : Iso (symm T)
      (productTensor (fun (π : Equiv.Perm (Fin 3)) i => d (π.symm i)) (fun π => perm π T)) := by
    apply iso_of_coordinates _ _ (fun i => (E i).trans (productDecode _).symm)
    intro x
    unfold symm productTensor
    apply Finset.prod_congr rfl
    intro π _
    apply congrArg (perm π T)
    funext i
    simp only [Function.comp_apply, Equiv.trans_apply, Equiv.apply_symm_apply]
    rfl
  rw [eval_iso φ hi, eval_productTensor]
  apply Finset.prod_congr rfl
  intro π _
  exact (eval_perm φ π T).symm

end OM.PolMul.Superadditivity
