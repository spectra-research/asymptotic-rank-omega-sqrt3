import Lib.OM.NNN7.Values

/-! Simultaneous extraction of all swapped digits, Route 1 (6)–(8).
The digit alphabets and the coefficient tensor are arbitrary. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN8
open CoordinateTensor OM.NNN.Raw OM.NNN2
set_option maxHeartbeats 1000000

variable {D : Type} [Fintype D] [LinearOrder D] {X : D → Type} [∀ h, Fintype (X h)]

abbrev Selected (X : D → Type) (s : Finset D) := ∀ h : {h // h ∈ s}, X h
abbrev Remaining (X : D → Type) (s : Finset D) := ∀ h : {h // h ∉ s}, X h

def fill (s : Finset D) (e : Selected X s) (r : Remaining X s) : ∀ h, X h :=
  fun h => if hh : h ∈ s then e ⟨h, hh⟩ else r ⟨h, hh⟩

lemma fill_mem (s : Finset D) (e : Selected X s) (r : Remaining X s)
    (h : D) (hh : h ∈ s) : fill s e r h = e ⟨h, hh⟩ := by
  simp [fill, hh]

lemma fill_not_mem (s : Finset D) (e : Selected X s) (r : Remaining X s)
    (h : D) (hh : h ∉ s) : fill s e r h = r ⟨h, hh⟩ := by
  simp [fill, hh]

/-- Permutation matrix swapping exactly the positions in `s` on a doubled bond. -/
def maskKernel (s : Finset D) (j q j' q' : ∀ h, X h) : ℂ :=
  ∏ h, if h ∈ s then OM.NNN7.swapKernel j q j' q' h
    else OM.NNN7.identityKernel j q j' q' h

lemma maskKernel_empty (j q j' q' : ∀ h, X h) :
    maskKernel ∅ j q j' q' = if j = j' ∧ q = q' then (1 : ℂ) else 0 := by
  simpa [maskKernel] using! OM.NNN7.identity_product j q j' q'

lemma maskKernel_eq_zero (s : Finset D) (j q j' q' : ∀ h, X h)
    (hne : (fun h : {h // h ∈ s} => q h) ≠ (fun h : {h // h ∈ s} => j' h)) :
    maskKernel s j q j' q' = 0 := by
  obtain ⟨⟨h, hh⟩, hd⟩ := Function.ne_iff.mp hne
  apply Finset.prod_eq_zero (Finset.mem_univ h)
  simp [hh, OM.NNN7.swapKernel, hd]

/-- The common output label on the whole selected set is free. -/
lemma maskKernel_fill (s : Finset D) (j q j' q' : ∀ h, X h)
    (e : Selected X s)
    (he : (fun h : {h // h ∈ s} => q h) = (fun h : {h // h ∈ s} => j' h)) :
    maskKernel s j q j' q' =
      maskKernel s j (fill s e (fun h => q h)) (fill s e (fun h => j' h)) q' := by
  apply Finset.prod_congr rfl
  intro h _
  by_cases hh : h ∈ s
  · have he' := congrFun he ⟨h, hh⟩
    simp [hh, OM.NNN7.swapKernel, fill_mem, he']
  · simp [hh, OM.NNN7.identityKernel, fill_not_mem]

def correction (T : Cube ℂ (∀ h, X h)) (s : Finset D) :
    Cube ℂ ((∀ h, X h) × (∀ h, X h)) :=
  fun a b c => ∑ j, ∑ q, T a.1 j c.1 * T q b.2 c.2 * maskKernel s j a.2 b.1 q

theorem correction_empty (T : Cube ℂ (∀ h, X h)) :
    correction T ∅ = tensorProduct T T := by
  funext a b c
  simp [correction, maskKernel_empty, tensorProduct, mul_ite, ite_and,
    Finset.sum_ite_irrel]

theorem correction_factorization (T : Cube ℂ (∀ h, X h)) (s : Finset D)
    (e : Selected X s) (a b c : (∀ h, X h) × (∀ h, X h)) :
    correction T s a b c =
      if (fun h : {h // h ∈ s} => a.2 h) = (fun h : {h // h ∈ s} => b.1 h) then
        correction T s (a.1, fill s e (fun h => a.2 h))
          (fill s e (fun h => b.1 h), b.2) c else 0 := by
  split_ifs with he
  · unfold correction
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro q _
    rw [maskKernel_fill s j a.2 b.1 q e he]
  · simp [correction, maskKernel_eq_zero s _ a.2 b.1 _ he]

/-- A literal rectangular restriction pays for all swapped digits at once.
This includes the empty mask and does not impose any condition on `T`. -/
theorem correction_restriction (T : Cube ℂ (∀ h, X h)) (s : Finset D)
    (e : Selected X s) :
    Restricts (squareSource ((∀ h, X h) × Remaining X s) (Selected X s))
      (correction T s) := by
  let left (a : (∀ h, X h) × (∀ h, X h)) :
      ((∀ h, X h) × Remaining X s) × Selected X s :=
    ((a.1, fun h => a.2 h), fun h => a.2 h)
  let right (b : (∀ h, X h) × (∀ h, X h)) :
      ((∀ h, X h) × Remaining X s) × Selected X s :=
    ((b.2, fun h => b.1 h), fun h => b.1 h)
  refine ⟨(fun a => identityRows _ (left a)), (fun b => identityRows _ (right b)),
    (fun c r => correction T s (r.1.1, fill s e r.1.2)
      (fill s e r.2.2, r.2.1) c), ?_⟩
  funext a b c
  rw [correction_factorization T s e a b c]
  simp [map_squareSource, identityRows, left, right, Prod.ext_iff, ite_mul, mul_ite,
    ite_and, Finset.sum_ite_irrel, Fintype.sum_prod_type]

end OM.NNN8
