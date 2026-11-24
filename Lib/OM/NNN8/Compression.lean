import Lib.OM.NNN8.Swaps

/-! A rank factorisation of any correlated swap kernel gives the literal
square-source payload. Signed corrections are paid at the same spectral point. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN8
open CoordinateTensor OM.NNN.Raw OM.NNN2
set_option maxHeartbeats 1000000

section Bond
variable {X R : Type} [Fintype X] [Fintype R]

def compressedLeft (T : Cube ℂ X) (U : R → X → X → ℂ) :
    (X × X) → X × R → ℂ := fun a r => ∑ j, U r.2 j a.2 * T a.1 j r.1

def compressedRight (T : Cube ℂ X) (V : R → X → X → ℂ) :
    (X × X) → X × R → ℂ := fun b r => ∑ q, V r.2 b.1 q * T q b.2 r.1

def contract (T : Cube ℂ X) (L : X → X → X → X → ℂ) : Cube ℂ (X × X) :=
  fun a b c => ∑ j, ∑ q, T a.1 j c.1 * T q b.2 c.2 * L j a.2 b.1 q

/-- Literal maps (5), valid also for a factorisation with no columns. -/
theorem factorized_payload (T : Cube ℂ X) (U V : R → X → X → ℂ) :
    mapTensor (compressedLeft T U) (compressedRight T V) (identityRows (X × X))
      (squareSource X R) = contract T (fun j q j' q' => ∑ p, U p j q * V p j' q') := by
  funext a b c
  simp only [map_squareSource, identityRows, Prod.ext_iff, mul_ite, mul_one,
    mul_zero, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [compressedLeft, compressedRight, contract, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro p _
  ring

lemma contract_add (T : Cube ℂ X) (L M : X → X → X → X → ℂ) :
    contract T (L + M) = contract T L + contract T M := by
  funext a b c
  simp [contract, mul_add, Finset.sum_add_distrib]

lemma contract_smul (T : Cube ℂ X) (z : ℂ) (L : X → X → X → X → ℂ) :
    contract T (z • L) = z • contract T L := by
  funext a b c
  simp only [contract, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  congr 1
  funext j
  congr 1
  funext q
  ring

lemma contract_sum {C : Type} (T : Cube ℂ X) (s : Finset C)
    (L : C → X → X → X → X → ℂ) :
    contract T (∑ c ∈ s, L c) = ∑ c ∈ s, contract T (L c) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    funext a b c
    simp [contract]
  | @insert c s hc ih => simp only [Finset.sum_insert hc, contract_add, ih]

end Bond

lemma restricts_smul {I J K A B C : Type} [Fintype I] [Fintype J] [Fintype K]
    {S : Tensor ℂ I J K} {T : Tensor ℂ A B C} (h : Restricts S T) (z : ℂ) :
    Restricts S (z • T) := by
  obtain ⟨u, v, w, rfl⟩ := h
  refine ⟨z • u, v, w, ?_⟩
  funext a b c
  simp only [mapTensor, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

section Digits
variable {D R C : Type} [Fintype D] [LinearOrder D] [Fintype R]
  {X : D → Type} [∀ h, Fintype (X h)]

/-- The identity coefficient is one; every other mask has its own correction.
Repeated and empty masks in the correction list are permitted. -/
theorem compressed_payload (T : Cube ℂ (∀ h, X h)) (s : Finset C)
    (mask : C → Finset D) (coeff : C → ℂ) (U V : R → (∀ h, X h) → (∀ h, X h) → ℂ)
    (hUV : ∀ j q j' q', (∑ p, U p j q * V p j' q') =
      maskKernel ∅ j q j' q' + ∑ c ∈ s, coeff c * maskKernel (mask c) j q j' q') :
    mapTensor (compressedLeft T U) (compressedRight T V)
      (identityRows ((∀ h, X h) × (∀ h, X h))) (squareSource (∀ h, X h) R) =
      tensorProduct T T + ∑ c ∈ s, coeff c • correction T (mask c) := by
  rw [factorized_payload]
  have he : (fun j q j' q' => ∑ p, U p j q * V p j' q') =
      maskKernel (X := X) ∅ + ∑ c ∈ s, coeff c • maskKernel (mask c) := by
    funext j q j' q'
    simpa using! hUV j q j' q'
  rw [he, contract_add, contract_sum]
  simp only [contract_smul]
  change correction T ∅ + ∑ c ∈ s, coeff c • correction T (mask c) = _
  rw [correction_empty]

/-- Source additivity and literal signed local maps prove the pointwise bound.
No tensor or source is maximised at a separate spectral point. -/
theorem compressed_value [∀ h, Nonempty (X h)]
    (φ : PolMul.Spectral ℂ) (T : Cube ℂ (∀ h, X h)) (s : Finset C)
    (mask : C → Finset D) (coeff : C → ℂ) (U V : R → (∀ h, X h) → (∀ h, X h) → ℂ)
    (hUV : ∀ j q j' q', (∑ p, U p j q * V p j' q') =
      maskKernel ∅ j q j' q' + ∑ c ∈ s, coeff c * maskKernel (mask c) j q j' q') :
    value φ (tensorProduct T T) ≤ value φ (squareSource (∀ h, X h) R) +
      ∑ c ∈ s, value φ (squareSource ((∀ h, X h) × Remaining X (mask c))
        (Selected X (mask c))) := by
  have h := OM.NNN7.remove_sum_value φ s (fun c => coeff c • correction T (mask c))
    (fun c => value φ (squareSource ((∀ h, X h) × Remaining X (mask c))
      (Selected X (mask c))))
    (fun c _ P => OM.NNN7.remove_correction_value φ P _ _
      (restricts_smul (correction_restriction T (mask c)
        (fun h => Classical.choice (inferInstance : Nonempty (X h)))) (coeff c)))
    (tensorProduct T T)
  rw [← compressed_payload T s mask coeff U V hUV] at h
  exact h.trans (add_le_add
    (value_map_le φ _ (compressedLeft T U) (compressedRight T V)
      (identityRows ((∀ h, X h) × (∀ h, X h)))) le_rfl)

end Digits

end OM.NNN8
