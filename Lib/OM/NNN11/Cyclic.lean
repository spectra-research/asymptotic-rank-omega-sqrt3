import Lib.OM.NNN11.Codes
import Lib.OM.NNN8.Factorization

/-! Seven-slot cyclic actions, the Fano difference set, and cheap characters. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN11
set_option maxHeartbeats 1000000

def fano : Finset (ZMod 7) := {0, 1, 3}

def crossings (c : ZMod 7) : Finset (ZMod 7) :=
  Finset.univ.filter (fun j => j ∈ fano ∧ j + c ∉ fano)

/-- Every nonzero shift has two crossings in each direction and one
intersection of the three-role set with its translate. -/
theorem fano_shift_counts : ∀ c : ZMod 7, c ≠ 0 →
    (crossings c).card = 2 ∧
    (Finset.univ.filter (fun j => j ∉ fano ∧ j + c ∈ fano)).card = 2 ∧
    (Finset.univ.filter (fun j => j ∈ fano ∧ j + c ∈ fano)).card = 1 := by
  decide +kernel

lemma crossings_zero : (crossings 0).card = 0 := by decide +kernel

theorem sum_crossings {N : ℕ} (c : Word N) :
    (∑ i, (crossings (c i)).card) = 2 * weight c := by
  have he (i : Fin N) : (crossings (c i)).card = if c i = 0 then 0 else 2 := by
    split_ifs with hi
    · rw [hi, crossings_zero]
    · exact (fano_shift_counts _ hi).1
  simp only [he]
  simp [weight, Finset.sum_ite, Nat.mul_comm]

abbrev Slots (N : ℕ) (X : Type) := Fin N → ZMod 7 → X

def shift {N : ℕ} {X : Type} (c : Word N) (x : Slots N X) : Slots N X :=
  fun i j => x i (j + c i)

lemma shift_zero {N : ℕ} {X : Type} (x : Slots N X) : shift 0 x = x := by
  funext i j
  simp [shift]

lemma shift_add {N : ℕ} {X : Type} (c d : Word N) (x : Slots N X) :
    shift (c + d) x = shift d (shift c x) := by
  funext i j
  simp [shift, add_assoc, add_comm, add_left_comm]

def cyclicAction {N : ℕ} {X : Type} (c : Word N) : Module.End ℂ (Slots N X → ℂ) where
  toFun f x := f (shift c x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma cyclicAction_zero {N : ℕ} {X : Type} : cyclicAction (N := N) (X := X) 0 = 1 := by
  ext f x
  simp [cyclicAction, shift_zero]

lemma cyclicAction_add {N : ℕ} {X : Type} (c d : Word N) :
    cyclicAction (X := X) (c + d) = cyclicAction c * cyclicAction d := by
  apply LinearMap.ext
  intro f
  funext x
  exact congrArg f (shift_add c d x)

def cyclicKernel {N : ℕ} {X : Type} (c : Word N) (x y : Slots N X) : ℂ :=
  if shift c x = y then 1 else 0

lemma slots_card (N : ℕ) (X : Type) [Fintype X] :
    Fintype.card (Slots N X) = Fintype.card X ^ (7 * N) := by
  simp [Slots, ← pow_mul]

/-- The projector is represented by actual endpoint factors, including rank zero.
The group is the message space, so no injectivity hypothesis is needed. -/
theorem exists_cyclic_factorization {N r : ℕ} {X : Type} [Fintype X]
    (code : Word r →ₗ[ZMod 7] Word N) :
    ∃ (χ : AddChar (Word r) ℂ) (R : ℕ) (U V : Fin R → Slots N X → ℂ),
      R * 7 ^ r ≤ Fintype.card X ^ (7 * N) ∧
      ∀ x y, (∑ p, U p x * V p y) =
        cyclicKernel 0 x y + ∑ c ∈ Finset.univ.erase (0 : Word r), χ c * cyclicKernel (code c) x y := by
  obtain ⟨χ, R, U, V, hR, hUV⟩ := NNN8.exists_character_factorization
    (fun c => cyclicAction (X := X) (code c))
    (by simp [cyclicAction_zero]) (by intro a b; simp [cyclicAction_add])
  refine ⟨χ, R, U, V, ?_, ?_⟩
  · simpa only [word_card, slots_card] using! hR
  · intro x y
    rw [hUV, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Word r))]
    simp [cyclicAction, cyclicKernel, Pi.single_apply, eq_comm]

end OM.NNN11
