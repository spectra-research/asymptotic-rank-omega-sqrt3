import Lib.OM.NNN3.Basic

/-! Digitwise symmetric columns and grouping by the largest swapped digit.
All identities hold for arbitrary digit alphabets and arbitrary coefficients. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN7
open OM.NNN3
set_option maxHeartbeats 1000000

variable {D : Type} [Fintype D] [LinearOrder D] {X : D → Type} [∀ h, Fintype (X h)]

def digitU (p : ∀ h, Sym2 (X h)) (j q : ∀ h, X h) : ℂ :=
  ∏ h, symU (p h) (j h) (q h)

def digitV (p : ∀ h, Sym2 (X h)) (j q : ∀ h, X h) : ℂ :=
  ∏ h, symV (p h) (j h) (q h)

def identityKernel (j q j' q' : ∀ h, X h) (h : D) : ℂ :=
  if j h = j' h ∧ q h = q' h then 1 else 0

def swapKernel (j q j' q' : ∀ h, X h) (h : D) : ℂ :=
  if j h = q' h ∧ q h = j' h then 1 else 0

/-- Equation (19): the complete paired bond is the product of identity-plus-swap kernels. -/
theorem digit_pairing (j q j' q' : ∀ h, X h) :
    (∑ p : ∀ h, Sym2 (X h), digitU p j q * digitV p j' q') =
      ∏ h, (identityKernel j q j' q' h + swapKernel j q j' q' h) := by
  simp only [digitU, digitV, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (κ := fun h => Sym2 (X h))
    (fun h p => symU p (j h) (q h) * symV p (j' h) (q' h))]
  apply Finset.prod_congr rfl
  intro h _
  exact sym_pairing (j h) (q h) (j' h) (q' h)

lemma identity_product (j q j' q' : ∀ h, X h) :
    (∏ h, identityKernel j q j' q' h) = (if j = j' ∧ q = q' then (1 : ℂ) else 0) := by
  by_cases he : j = j' ∧ q = q'
  · rcases he with ⟨rfl, rfl⟩
    simp [identityKernel]
  · rw [if_neg he]
    have hex : ∃ h, ¬(j h = j' h ∧ q h = q' h) := by
      by_contra hh
      push_neg at hh
      exact he ⟨funext (fun h => (hh h).1), funext (fun h => (hh h).2)⟩
    obtain ⟨h, hh⟩ := hex
    apply Finset.prod_eq_zero (Finset.mem_univ h)
    simp [identityKernel, hh]

def groupedKernel (j q j' q' : ∀ h, X h) (h : D) : ℂ :=
  swapKernel j q j' q' h *
    (∏ g ∈ Finset.univ.filter (· < h), (identityKernel j q j' q' g + swapKernel j q j' q' g)) *
    ∏ g ∈ Finset.univ.filter (h < ·), identityKernel j q j' q' g

/-- Equation (20), including the untouched higher digits. Each nonempty swap set
appears exactly once, grouped by its largest element. -/
theorem grouped_pairing (j q j' q' : ∀ h, X h) :
    (∑ p : ∀ h, Sym2 (X h), digitU p j q * digitV p j' q') =
      (if j = j' ∧ q = q' then (1 : ℂ) else 0) + ∑ h, groupedKernel j q j' q' h := by
  rw [digit_pairing, Finset.prod_add_ordered, identity_product]
  rfl

/-- The chosen output digit is a free equality edge in its entire correction. -/
theorem groupedKernel_eq_zero (j q j' q' : ∀ h, X h) (h : D)
    (hne : q h ≠ j' h) : groupedKernel j q j' q' h = 0 := by
  simp [groupedKernel, swapKernel, hne]

end OM.NNN7
