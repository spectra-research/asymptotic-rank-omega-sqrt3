import Lib.OM.NNN7.Compression

/-! Literal rectangular source for each grouped correction.
The removed output digit is an equality edge; every remaining coefficient lives
in the third local map. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN7
open CoordinateTensor OM.NNN.Raw OM.NNN2
set_option maxHeartbeats 1000000
variable {D : Type} [Fintype D] [LinearOrder D] {X : D → Type} [∀ h, Fintype (X h)]

abbrev Rest (X : D → Type) (h : D) := ∀ g : {g : D // g ≠ h}, X g

def fill (h : D) (e : X h) (r : Rest X h) : ∀ g, X g :=
  (Equiv.piSplitAt h X).symm (e, r)

lemma fill_self (h : D) (e : X h) (r : Rest X h) : fill h e r h = e := by
  simp [fill, Equiv.piSplitAt]

lemma fill_ne (h : D) (e : X h) (r : Rest X h) (g : D) (hg : g ≠ h) :
    fill h e r g = r ⟨g, hg⟩ := by
  simp [fill, Equiv.piSplitAt, hg]

/-- Replacing the common output digit leaves the entire grouped kernel unchanged. -/
lemma groupedKernel_fill (j q j' q' : ∀ h, X h) (h : D) (e : X h)
    (he : q h = j' h) :
    groupedKernel j q j' q' h =
      groupedKernel j (fill h e (fun g => q g)) (fill h e (fun g => j' g)) q' h := by
  have hid (g : D) (hg : g ≠ h) :
      identityKernel j q j' q' g =
        identityKernel j (fill h e (fun g => q g)) (fill h e (fun g => j' g)) q' g := by
    simp [identityKernel, fill_ne _ _ _ _ hg]
  have hsw (g : D) (hg : g ≠ h) :
      swapKernel j q j' q' g =
        swapKernel j (fill h e (fun g => q g)) (fill h e (fun g => j' g)) q' g := by
    simp [swapKernel, fill_ne _ _ _ _ hg]
  unfold groupedKernel
  apply congrArg₂ (fun x y : ℂ => x * y)
  · apply congrArg₂ (fun x y : ℂ => x * y)
    · simp [swapKernel, fill_self, he]
    · apply Finset.prod_congr rfl
      intro g hg
      have hne : g ≠ h := ne_of_lt (Finset.mem_filter.mp hg).2
      rw [hid g hne, hsw g hne]
  · apply Finset.prod_congr rfl
    intro g hg
    exact hid g (ne_of_gt (Finset.mem_filter.mp hg).2)

theorem correction_factorization (T : Cube ℂ (∀ h, X h)) (h : D) (e : X h)
    (a b c : (∀ h, X h) × (∀ h, X h)) :
    correction T h a b c =
      if a.2 h = b.1 h then
        correction T h (a.1, fill h e (fun g => a.2 g))
          (fill h e (fun g => b.1 g), b.2) c else 0 := by
  split_ifs with he
  · unfold correction
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro q _
    rw [groupedKernel_fill j a.2 b.1 q h e he]
  · exact correction_eq_zero T h a b c he

/-- Each correction is a literal restriction of K(L_h,L_h,m_h), with
L_h the cardinality of `coordinates × remaining digits`. -/
theorem correction_restriction (T : Cube ℂ (∀ h, X h)) (h : D) (e : X h) :
    Restricts (squareSource ((∀ g, X g) × Rest X h) (X h)) (correction T h) := by
  let left (a : (∀ g, X g) × (∀ g, X g)) : ((∀ g, X g) × Rest X h) × X h :=
    ((a.1, fun g => a.2 g), a.2 h)
  let right (b : (∀ g, X g) × (∀ g, X g)) : ((∀ g, X g) × Rest X h) × X h :=
    ((b.2, fun g => b.1 g), b.1 h)
  refine ⟨(fun a => identityRows _ (left a)), (fun b => identityRows _ (right b)),
    (fun c r => correction T h (r.1.1, fill h e r.1.2) (fill h e r.2.2, r.2.1) c), ?_⟩
  funext a b c
  rw [correction_factorization T h e a b c]
  simp [map_squareSource, identityRows, left, right, Prod.ext_iff, ite_mul, mul_ite,
    ite_and, Finset.sum_ite_irrel, Fintype.sum_prod_type]

end OM.NNN7
