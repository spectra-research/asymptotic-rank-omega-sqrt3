import Lib.OM.NNN7.Kernels

/-! Exact tensor contraction for all digitwise compressions at once. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN7
open CoordinateTensor OM.NNN.Raw OM.NNN2
set_option maxHeartbeats 1000000
variable {D : Type} [Fintype D] [LinearOrder D] {X : D → Type} [∀ h, Fintype (X h)]

def compressedLeft (T : Cube ℂ (∀ h, X h)) :
    ((∀ h, X h) × (∀ h, X h)) → (∀ h, X h) × (∀ h, Sym2 (X h)) → ℂ :=
  fun a r => ∑ j, digitU r.2 j a.2 * T a.1 j r.1

def compressedRight (T : Cube ℂ (∀ h, X h)) :
    ((∀ h, X h) × (∀ h, X h)) → (∀ h, X h) × (∀ h, Sym2 (X h)) → ℂ :=
  fun b r => ∑ q, digitV r.2 b.1 q * T q b.2 r.1

def correction (T : Cube ℂ (∀ h, X h)) (h : D) : Cube ℂ ((∀ h, X h) × (∀ h, X h)) :=
  fun a b c => ∑ j, ∑ q, T a.1 j c.1 * T q b.2 c.2 * groupedKernel j a.2 b.1 q h

/-- The complete image contains exactly one grouped correction for each digit. -/
theorem compressed_payload (T : Cube ℂ (∀ h, X h)) :
    mapTensor (compressedLeft T) (compressedRight T)
      (identityRows ((∀ h, X h) × (∀ h, X h)))
      (squareSource (∀ h, X h) (∀ h, Sym2 (X h))) = tensorProduct T T + ∑ h, correction T h := by
  funext a b c
  simp only [map_squareSource, identityRows, Prod.ext_iff, mul_ite, mul_one,
    mul_zero, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [compressedLeft, compressedRight, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
  have hp (j q : ∀ h, X h) :
      (∑ p : ∀ h, Sym2 (X h), digitU p j a.2 * T a.1 j c.1 *
          (digitV p b.1 q * T q b.2 c.2)) =
        (T a.1 j c.1 * T q b.2 c.2) *
          ((if j = b.1 ∧ a.2 = q then 1 else 0) + ∑ h, groupedKernel j a.2 b.1 q h) := by
    rw [← grouped_pairing j a.2 b.1 q, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  simp only [hp, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  have he : (∑ q, ∑ j, T a.1 j c.1 * T q b.2 c.2 *
      (if j = b.1 ∧ a.2 = q then (1 : ℂ) else 0)) = tensorProduct T T a b c := by
    simp [tensorProduct, mul_ite, ite_and, Finset.sum_ite_irrel]
  rw [he]
  simp only [Pi.add_apply, Finset.sum_apply, correction]
  congr 1
  rw [Finset.sum_comm]
  calc
    _ = ∑ j, ∑ h, ∑ q, T a.1 j c.1 * T q b.2 c.2 * groupedKernel j a.2 b.1 q h := by
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- Support of each correction includes the chosen equality edge. -/
theorem correction_eq_zero (T : Cube ℂ (∀ h, X h)) (h : D)
    (a b c : (∀ h, X h) × (∀ h, X h)) (hne : a.2 h ≠ b.1 h) :
    correction T h a b c = 0 := by
  simp [correction, groupedKernel_eq_zero _ _ _ _ h hne]

end OM.NNN7
