import Lib.OM.NNN12.Tiles
import Lib.OM.NNN11.Layout

/-! Actual physical bond layouts with their alphabet, extraction multiplicity
and ordinary character rank factorization. All high coordinates are retained. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN12
open NNN11.Network NNN11.SlotExtraction NNN11.Wiring
open NNN11.ExtractionAB (X Slot permutationBond bitBasis)
open Codes
set_option maxHeartbeats 1500000

structure BondLayout (q k : ℕ) [Fact q.Prime] (A B : Type) [Fintype A] [Fintype B]
    (x y N : ℕ) where
  High : Type
  finiteHigh : Fintype High
  coordinates : Slot A B x y ≃ (Fin N × ZMod q) ⊕ High
  crossings : ∀ c : Word q N,
    Fintype.card (EqualSlots (Cyclic.permutation coordinates c)
      (Cyclic.active coordinates c)) = k * weight c

attribute [instance] BondLayout.finiteHigh

namespace BondLayout
variable {q k : ℕ} [Fact q.Prime] {A B : Type} [Fintype A] [Fintype B] {x y N : ℕ}

def ofTiles {b : ℕ} (D : Finset (ZMod q)) (hD : Cyclic.ShiftCounts D k)
    (e : (A ⊕ B) ≃ Fin b × ZMod q) (flip : Fin b → Bool)
    (hr : ∀ p, slotRole (e.symm p) ↔ Cyclic.tileRole D flip p) (x y : ℕ) :
    BondLayout q k A B x y (b * min x y) where
  High := BondCoordinates.High A B x y (min x y)
  finiteHigh := inferInstance
  coordinates := BondCoordinates.layout e (min_le_left x y) (min_le_right x y)
  crossings c := by
    apply Cyclic.transported_selected_card _ D hD
      (fun i => flip (finProdFinEquiv.symm i).1) c slotRole
    intro p
    rw [BondCoordinates.layout_role, hr]
    rfl

variable (L : BondLayout q k A B x y N)

def kernel (c : Word q N) : Operator (BondAB A B (X x) (X y)) :=
  permutationBond (Cyclic.permutation L.coordinates c)

lemma kernel_zero : L.kernel 0 = identity _ := by
  rw [kernel, Cyclic.permutation_zero, NNN11.ExtractionAB.permutationBond_refl]

include L

lemma length_bound : q * N ≤ Fintype.card A * y + Fintype.card B * x := by
  have h := Fintype.card_congr L.coordinates
  simp only [Slot, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, ZMod.card,
    show N * q = q * N from Nat.mul_comm _ _] at h
  omega

lemma message_card_le {r : ℕ} (hr : r ≤ N) :
    q ^ r ≤ 2 ^ (Fintype.card A * y + Fintype.card B * x) := by
  calc
    q ^ r ≤ (2 ^ q) ^ r := Nat.pow_le_pow_left (Nat.lt_two_pow_self.le) _
    _ = 2 ^ (q * r) := (pow_mul 2 q r).symm
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) ((Nat.mul_le_mul_left q hr).trans L.length_bound)

lemma head_base_ge_one {r : ℕ} (hr : r ≤ N) :
    1 ≤ (2 : ℝ) ^ (Fintype.card A * y + Fintype.card B * x) / (q : ℝ) ^ r := by
  have hq : (0 : ℝ) < q := Nat.cast_pos.mpr (Fact.out : Nat.Prime q).pos
  apply (le_div_iff₀ (pow_pos hq r)).2
  simpa only [one_mul] using! (show (q : ℝ) ^ r ≤
    (2 : ℝ) ^ (Fintype.card A * y + Fintype.card B * x) by exact_mod_cast L.message_card_le hr)

theorem factorization {r : ℕ} (code : Word q r →ₗ[ZMod q] Word q N) :
    ∃ (χ : AddChar (Word q r) ℂ) (R : ℕ)
      (U V : Fin R → BondAB A B (X x) (X y) → ℂ),
      R * q ^ r ≤ 2 ^ (Fintype.card A * y + Fintype.card B * x) ∧
      ∀ u v, (∑ p, U p u * V p v) = identity _ u v +
        ∑ c ∈ Finset.univ.erase (0 : Word q r), χ c * L.kernel (code c) u v := by
  obtain ⟨χ, R, U, V, hR, hUV⟩ := Codes.exists_permutation_factorization
    (bitBasis A B x y) (Cyclic.permutation L.coordinates)
    (Cyclic.permutation_zero L.coordinates) (Cyclic.permutation_add L.coordinates) code
  refine ⟨χ, R, U, V, ?_, ?_⟩
  · simpa only [bondAB_card, X, Fintype.card_fun, ZMod.card,
      Fintype.card_fin, ← pow_mul, ← pow_add, Nat.mul_comm] using! hR
  · intro u v
    have hk (π : Slot A B x y ≃ Slot A B x y) :
        NNN11.PermutationCodes.kernel (bitBasis A B x y) π = permutationBond π := by
      funext w z
      simp only [NNN11.PermutationCodes.kernel, permutationBond, delta, Relation, forall_const]
      split_ifs <;> rfl
    simpa only [hk] using! hUV u v

end BondLayout

namespace Layouts

def heavy28 (x y : ℕ) : BondLayout 3 1 (Fin 7) (Fin 14) x y (7 * min x y) :=
  BondLayout.ofTiles Cyclic.d3 Cyclic.d3_counts.2 Tiles.heavy3 (fun _ => false)
    (Tiles.inverse_role _ _ Tiles.heavy3_left Tiles.heavy3_right) x y

def heavy112 (x y : ℕ) : BondLayout 11 3 (Fin 35) (Fin 42) x y (7 * min x y) :=
  BondLayout.ofTiles Cyclic.d11 Cyclic.d11_counts.2 Tiles.heavy11 (fun _ => false)
    (Tiles.inverse_role _ _ Tiles.heavy11_left Tiles.heavy11_right) x y

def heavy196 (x y : ℕ) : BondLayout 19 5 (Fin 63) (Fin 70) x y (7 * min x y) :=
  BondLayout.ofTiles Cyclic.d19 Cyclic.d19_counts.2 Tiles.heavy19 (fun _ => false)
    (Tiles.inverse_role _ _ Tiles.heavy19_left Tiles.heavy19_right) x y

def light28 (x y : ℕ) : BondLayout 7 2 (Fin 7) (Fin 7) x y (2 * min x y) :=
  BondLayout.ofTiles NNN11.fano Cyclic.d7_counts.2 Tiles.light28
    (fun i => if i.val < 1 then false else true) (by
      intro p
      rw [Tiles.inverse_role _ _ Tiles.light28_roles.1 Tiles.light28_roles.2]
      simp only [Tiles.balancedRole, Cyclic.tileRole, Cyclic.role]
      split_ifs <;> simp_all) x y

def light112 (x y : ℕ) : BondLayout 7 2 (Fin 35) (Fin 35) x y (10 * min x y) :=
  BondLayout.ofTiles NNN11.fano Cyclic.d7_counts.2 Tiles.light112
    (fun i => if i.val < 5 then false else true) (by
      intro p
      rw [Tiles.inverse_role _ _ Tiles.light112_roles.1 Tiles.light112_roles.2]
      simp only [Tiles.balancedRole, Cyclic.tileRole, Cyclic.role]
      split_ifs <;> simp_all) x y

def light196 (x y : ℕ) : BondLayout 7 2 (Fin 63) (Fin 63) x y (18 * min x y) :=
  BondLayout.ofTiles NNN11.fano Cyclic.d7_counts.2 Tiles.light196
    (fun i => if i.val < 9 then false else true) (by
      intro p
      rw [Tiles.inverse_role _ _ Tiles.light196_roles.1 Tiles.light196_roles.2]
      simp only [Tiles.balancedRole, Cyclic.tileRole, Cyclic.role]
      split_ifs <;> simp_all) x y

lemma reverse_role {A B P : Type} (e : (A ⊕ B) ≃ P) (r : P → Prop)
    (hr : ∀ p, slotRole (e.symm p) ↔ r p) (p : P) :
    slotRole (((Equiv.sumComm B A).trans e).symm p) ↔ ¬ r p := by
  have h := hr p
  cases he : e.symm p <;> simpa [he, slotRole] using! not_congr h

def reverseHeavy28 (x y : ℕ) : BondLayout 3 1 (Fin 14) (Fin 7) x y (7 * min x y) :=
  BondLayout.ofTiles Cyclic.d3 Cyclic.d3_counts.2 ((Equiv.sumComm _ _).trans Tiles.heavy3)
    (fun _ => true) (reverse_role _ _ (Tiles.inverse_role _ _ Tiles.heavy3_left Tiles.heavy3_right)) x y

def reverseHeavy112 (x y : ℕ) : BondLayout 11 3 (Fin 42) (Fin 35) x y (7 * min x y) :=
  BondLayout.ofTiles Cyclic.d11 Cyclic.d11_counts.2 ((Equiv.sumComm _ _).trans Tiles.heavy11)
    (fun _ => true) (reverse_role _ _ (Tiles.inverse_role _ _ Tiles.heavy11_left Tiles.heavy11_right)) x y

def reverseHeavy196 (x y : ℕ) : BondLayout 19 5 (Fin 70) (Fin 63) x y (7 * min x y) :=
  BondLayout.ofTiles Cyclic.d19 Cyclic.d19_counts.2 ((Equiv.sumComm _ _).trans Tiles.heavy19)
    (fun _ => true) (reverse_role _ _ (Tiles.inverse_role _ _ Tiles.heavy19_left Tiles.heavy19_right)) x y

end Layouts

end OM.NNN12
