import Lib.OM.NNN11.Network70
import Lib.OM.NNN11.OrientedRetention

/-! Physical bond layouts, retaining their coordinate maps and crossing counts. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN11
open CoordinateTensor OM.NNN.Raw OM.NNN2 Network SlotExtraction Wiring
open ExtractionAB (X Slot permutationBond)
set_option maxHeartbeats 1000000

structure BondLayout (A B : Type) [Fintype A] [Fintype B] (x y N : ℕ) where
  High : Type
  finiteHigh : Fintype High
  coordinates : Slot A B x y ≃ (Fin N × ZMod 7) ⊕ High
  crossings : ∀ c : Word N,
    Fintype.card (EqualSlots (MixedCrossings.permutation coordinates c)
      (MixedCrossings.active coordinates c)) = 2 * weight c

attribute [instance] BondLayout.finiteHigh

namespace BondLayout
variable {A B : Type} [Fintype A] [Fintype B] {x y N : ℕ}
  (L : BondLayout A B x y N)

def kernel (c : Word N) : Operator (BondAB A B (X x) (X y)) :=
  permutationBond (MixedCrossings.permutation L.coordinates c)

lemma kernel_zero : L.kernel 0 = Network.identity _ := by
  rw [kernel, MixedCrossings.permutation_zero, ExtractionAB.permutationBond_refl]

include L

lemma length_bound : 7 * N ≤ Fintype.card A * y + Fintype.card B * x := by
  have h := Fintype.card_congr L.coordinates
  simp only [Slot, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, ZMod.card] at h
  omega

lemma message_card_le {r : ℕ} (hr : r ≤ N) : 7 ^ r ≤ 2 ^ (Fintype.card A * y + Fintype.card B * x) := by
  calc
    7 ^ r ≤ (2 ^ 7) ^ r := Nat.pow_le_pow_left (by norm_num) _
    _ = 2 ^ (7 * r) := (pow_mul 2 7 r).symm
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) ((Nat.mul_le_mul_left 7 hr).trans L.length_bound)

lemma head_base_ge_one {r : ℕ} (hr : r ≤ N) :
    1 ≤ (2 : ℝ) ^ (Fintype.card A * y + Fintype.card B * x) / (7 : ℝ) ^ r := by
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (7 : ℝ) ^ r)).2
  simpa only [one_mul] using! (show (7 : ℝ) ^ r ≤
    (2 : ℝ) ^ (Fintype.card A * y + Fintype.card B * x) by exact_mod_cast L.message_card_le hr)

theorem factorization {r : ℕ} (code : Word r →ₗ[ZMod 7] Word N) :
    ∃ (χ : AddChar (Word r) ℂ) (R : ℕ)
      (U V : Fin R → BondAB A B (X x) (X y) → ℂ),
      R * 7 ^ r ≤ 2 ^ (Fintype.card A * y + Fintype.card B * x) ∧
      ∀ u v, (∑ p, U p u * V p v) = Network.identity _ u v +
        ∑ c ∈ Finset.univ.erase (0 : Word r), χ c * L.kernel (code c) u v := by
  obtain ⟨χ, R, U, V, hR, hUV⟩ := ExtractionAB.exists_network_factorization L.coordinates code
  refine ⟨χ, R, U, V, ?_, hUV⟩
  simpa only [bondAB_card, X, Fintype.card_fun, ZMod.card,
    Fintype.card_fin, ← pow_mul, ← pow_add, Nat.mul_comm] using! hR

end BondLayout

namespace BondCoordinates

def light (x y : ℕ) : BondLayout (Fin 21) (Fin 21) x y (6 * min x y) where
  High := _
  finiteHigh := inferInstance
  coordinates := lightLayout x y
  crossings := light_selected_card x y

def heavy (x y : ℕ) : BondLayout (Fin 21) (Fin 28) x y (7 * min x y) where
  High := _
  finiteHigh := inferInstance
  coordinates := heavyLayout x y
  crossings := heavy_selected_card x y

def reverseHeavy (x y : ℕ) : BondLayout (Fin 28) (Fin 21) x y (7 * min x y) where
  High := _
  finiteHigh := inferInstance
  coordinates := reverseHeavyLayout x y
  crossings := reverse_heavy_selected_card x y

end BondCoordinates
end OM.NNN11
