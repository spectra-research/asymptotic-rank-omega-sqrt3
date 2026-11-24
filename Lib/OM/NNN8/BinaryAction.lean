import Lib.OM.NNN8.Compression
import Lib.OM.NNN8.Factorization

/-! Binary masks act on doubled coordinate words by commuting digit swaps. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN8
open CoordinateTensor OM.NNN.Raw
set_option maxHeartbeats 1000000

variable {D : Type} [Fintype D] [LinearOrder D]
  {X : D → Type} [∀ h, Fintype (X h)]

def binaryMask (c : D → ZMod 2) : Finset D := Finset.univ.filter (fun h => c h ≠ 0)

def swapPair (c : D → ZMod 2) (x : (∀ h, X h) × (∀ h, X h)) :
    (∀ h, X h) × (∀ h, X h) :=
  (fun h => if c h = 0 then x.1 h else x.2 h,
   fun h => if c h = 0 then x.2 h else x.1 h)

lemma swapPair_zero (x : (∀ h, X h) × (∀ h, X h)) : swapPair 0 x = x := by
  ext h <;> simp [swapPair]

lemma swapPair_add (c d : D → ZMod 2) (x : (∀ h, X h) × (∀ h, X h)) :
    swapPair (c + d) x = swapPair d (swapPair c x) := by
  have cases₂ (a : ZMod 2) : a = 0 ∨ a = 1 := by fin_cases a <;> simp
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide +kernel
  apply Prod.ext <;> funext h <;>
    rcases cases₂ (c h) with hc | hc <;> rcases cases₂ (d h) with hd | hd <;>
    simp [swapPair, hc, hd, h11]

def swapAction (c : D → ZMod 2) :
    Module.End ℂ (((∀ h, X h) × (∀ h, X h)) → ℂ) where
  toFun f x := f (swapPair c x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma swapAction_zero : swapAction (X := X) 0 = 1 := by
  ext f x
  simp [swapAction, swapPair_zero]

lemma swapAction_add (c d : D → ZMod 2) :
    swapAction (X := X) (c + d) = swapAction c * swapAction d := by
  apply LinearMap.ext
  intro f
  funext x
  exact congrArg f (swapPair_add c d x)

lemma maskKernel_swapPair (c : D → ZMod 2) (j q j' q' : ∀ h, X h) :
    maskKernel (binaryMask c) j q j' q' =
      if swapPair c (j, q) = (j', q') then (1 : ℂ) else 0 := by
  simp only [Prod.ext_iff]
  rw [← OM.NNN7.identity_product]
  apply Finset.prod_congr rfl
  intro h _
  by_cases hc : c h = 0
  · simp [binaryMask, hc, OM.NNN7.identityKernel, swapPair]
  · simp [binaryMask, hc, OM.NNN7.identityKernel, OM.NNN7.swapKernel,
      swapPair, and_comm]

lemma swapAction_entry (c : D → ZMod 2) (i j : (∀ h, X h) × (∀ h, X h)) :
    swapAction c (Pi.single j 1) i = maskKernel (binaryMask c) i.1 i.2 j.1 j.2 := by
  rw [maskKernel_swapPair]
  simp [swapAction, Pi.single_apply, eq_comm]

/-- Choose the cheapest character after the additive family of masks is fixed.
The mask map need not be injective. -/
theorem exists_swap_factorization {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (code : G →+ (D → ZMod 2)) :
    ∃ (χ : AddChar G ℂ) (r : ℕ)
      (U V : Fin r → (∀ h, X h) → (∀ h, X h) → ℂ),
      r * Fintype.card G ≤ (Fintype.card (∀ h, X h)) ^ 2 ∧
      ∀ j q j' q', (∑ p, U p j q * V p j' q') =
        maskKernel ∅ j q j' q' +
          ∑ c ∈ Finset.univ.erase (0 : G), χ c * maskKernel (binaryMask (code c)) j q j' q' := by
  obtain ⟨χ, r, U, V, hr, hUV⟩ := exists_character_factorization
    (fun c => swapAction (X := X) (code c))
    (by simp [swapAction_zero]) (by intro a b; simp [swapAction_add])
  refine ⟨χ, r, (fun p j q => U p (j, q)), (fun p j q => V p (j, q)), ?_, ?_⟩
  · simpa [Fintype.card_prod, pow_two] using! hr
  · intro j q j' q'
    calc
      _ = ∑ g, χ g * maskKernel (binaryMask (code g)) j q j' q' := by
        rw [hUV]
        apply Finset.sum_congr rfl
        intro g _
        congr 1
        by_cases he : swapPair (code g) (j, q) = (j', q') <;>
          simpa [swapAction, Pi.single_apply, he] using!
            (swapAction_entry (X := X) (code g) (j, q) (j', q'))
      _ = _ := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : G))]
        simp [binaryMask]

end OM.NNN8
