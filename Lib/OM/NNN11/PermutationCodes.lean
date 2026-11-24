import Lib.OM.NNN11.BondCoordinates

/-! Cheap characters for precisely the permutation kernels used by the literal
extraction theorem, including dependent generators and empty factor spaces. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN11.PermutationCodes
open Network Wiring
set_option maxHeartbeats 1000000

variable {S E D : Type} (e : E ≃ (S → D))

def shift (π : S ≃ S) (w : E) : E := e.symm (fun s => e w (π.symm s))

lemma shift_refl (w : E) : shift e (Equiv.refl S) w = w := by
  simp [shift]

lemma shift_trans (π τ : S ≃ S) (w : E) :
    shift e (π.trans τ) w = shift e τ (shift e π w) := by
  simp [shift]

lemma shift_eq_iff (π : S ≃ S) (u v : E) :
    shift e π u = v ↔ ∀ s, e u s = e v (π s) := by
  constructor
  · intro h s
    have he := congrArg (fun w => e w (π s)) h
    simpa [shift] using! he
  · intro h
    apply e.injective
    funext s
    simpa [shift] using! h (π.symm s)

def action (π : S ≃ S) : Module.End ℂ (E → ℂ) where
  toFun f w := f (shift e π w)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma action_refl : action e (Equiv.refl S) = 1 := by
  ext f w
  simp [action, shift_refl]

lemma action_trans (π τ : S ≃ S) : action e (π.trans τ) = action e π * action e τ := by
  ext f w
  exact congrArg f (shift_trans e π τ w)

def kernel (π : S ≃ S) (u v : E) : ℂ := if ∀ s, e u s = e v (π s) then 1 else 0

lemma kernel_refl : kernel e (Equiv.refl S) = Network.identity E := by
  funext u v
  have he : (∀ s, e u s = e v s) ↔ u = v := by
    rw [← funext_iff, e.injective.eq_iff]
  simp only [kernel, Equiv.refl_apply, he, Network.identity]

theorem exists_factorization [Fintype E] {N r : ℕ}
    (π : Word N → S ≃ S) (hzero : π 0 = Equiv.refl S)
    (hadd : ∀ c d, π (c + d) = (π c).trans (π d))
    (code : Word r →ₗ[ZMod 7] Word N) :
    ∃ (χ : AddChar (Word r) ℂ) (R : ℕ) (U V : Fin R → E → ℂ),
      R * 7 ^ r ≤ Fintype.card E ∧
      ∀ u v, (∑ p, U p u * V p v) = Network.identity E u v +
        ∑ c ∈ Finset.univ.erase (0 : Word r), χ c * kernel e (π (code c)) u v := by
  obtain ⟨χ, R, U, V, hR, hUV⟩ := NNN8.exists_character_factorization
    (fun c => action e (π (code c)))
    (by simp [hzero, action_refl]) (by intro a b; simp [hadd, action_trans])
  refine ⟨χ, R, U, V, ?_, ?_⟩
  · simpa only [word_card] using! hR
  · intro u v
    have hk (c : Word r) : action e (π (code c)) (Pi.single v 1) u = kernel e (π (code c)) u v := by
      simp only [action, LinearMap.coe_mk, AddHom.coe_mk, Pi.single_apply]
      rw [shift_eq_iff]
      rfl
    rw [hUV]
    simp_rw [hk]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Word r))]
    simp only [map_zero, hzero, kernel_refl, AddChar.map_zero_eq_one, one_mul]

end OM.NNN11.PermutationCodes

namespace OM.NNN11.MixedCrossings
variable {S H : Type} {N : ℕ} (e : S ≃ (Fin N × ZMod 7) ⊕ H)

lemma permutation_zero : permutation e 0 = Equiv.refl S := by
  ext s
  apply e.injective
  simp only [permutation, Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.refl_apply]
  cases e s <;> simp [tilePerm]

lemma permutation_add (c d : Word N) :
    permutation e (c + d) = (permutation e c).trans (permutation e d) := by
  ext s
  apply e.injective
  simp only [permutation, Equiv.trans_apply, Equiv.apply_symm_apply]
  cases e s <;> simp [tilePerm, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]

end OM.NNN11.MixedCrossings

namespace OM.NNN11.ExtractionAB
open Network Wiring
variable {A B : Type} [Fintype A] [Fintype B] {x y N r : ℕ} {H : Type}
  (e : Slot A B x y ≃ (Fin N × ZMod 7) ⊕ H)

theorem exists_network_factorization (code : Word r →ₗ[ZMod 7] Word N) :
    ∃ (χ : AddChar (Word r) ℂ) (R : ℕ)
      (U V : Fin R → BondAB A B (X x) (X y) → ℂ),
      R * 7 ^ r ≤ Fintype.card (BondAB A B (X x) (X y)) ∧
      ∀ u v, (∑ p, U p u * V p v) = Network.identity _ u v +
        ∑ c ∈ Finset.univ.erase (0 : Word r),
          χ c * permutationBond (MixedCrossings.permutation e (code c)) u v := by
  obtain ⟨χ, R, U, V, hR, hUV⟩ := PermutationCodes.exists_factorization
    (bitBasis A B x y) (MixedCrossings.permutation e)
    (MixedCrossings.permutation_zero e) (MixedCrossings.permutation_add e) code
  refine ⟨χ, R, U, V, hR, ?_⟩
  intro u v
  have hk (π : Slot A B x y ≃ Slot A B x y) :
      PermutationCodes.kernel (bitBasis A B x y) π = permutationBond π := by
    funext w z
    simp only [PermutationCodes.kernel, permutationBond, delta, Relation, forall_const]
    split_ifs <;> rfl
  simpa only [hk] using! hUV u v

end OM.NNN11.ExtractionAB
