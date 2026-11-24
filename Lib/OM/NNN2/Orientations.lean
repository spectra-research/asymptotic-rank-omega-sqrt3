import Lib.OM.NNN2.Square
import Foundations.Tensors.OrientationTransport

noncomputable section
open scoped BigOperators Classical
set_option maxHeartbeats 1000000
namespace OM.NNN2
open Semicontinuity Foundations.PairUnitExponents Foundations.OrientationTransport

/-- The tensor and the spectral point are transported together, so the value
on the left is that of the original ordered tensor in every orientation. -/
theorem oriented_inequalities (φ : PolMul.Spectral ℂ) (n : ℕ+)
    (T : KTensor ℂ (fun _ : Fin 3 => n)) (i : Fin 3) :
    let x := PolMul.Spectral.eval φ T
    let v := fun j => (n : ℝ) ^ theta φ j
    (x ^ 2 + (v i) ^ 2 * x ≤ (∏ j, v j) * v i + (v i) ^ 2 * ((∑ j, v j) - v i)) ∧
    x ^ 2 ≤ (∏ j, v j) * v i := by
  let σ := rot i
  let ψ := pullPoint φ σ
  let S : KTensor ℂ (fun _ : Fin 3 => n) := KTensor.legReindex σ T
  have h := square_inequalities ψ n S
  have hx : PolMul.Spectral.eval ψ S = PolMul.Spectral.eval φ T := by
    change AsymptoticSpectrumDuality.AsymptoticSpectrum.eval _
      (legPermEquiv σ (legPermEquiv σ (TensorClass.mk ⟨_, T⟩))) φ = _
    rw [legPermEquiv_rot_rot]
    rfl
  dsimp only at h ⊢
  rw [hx] at h
  have ht (j : Fin 3) : theta ψ j = theta φ (σ.symm j) := theta_legReindex φ σ j
  simp only [ht, Fin.prod_univ_three, Fin.sum_univ_three] at h ⊢
  have hr0 : rot (0 : Fin 3) = Equiv.swap 0 2 := rfl
  have hr1 : rot (1 : Fin 3) = Equiv.swap 1 2 := rfl
  have hr2 : rot (2 : Fin 3) = 1 := rfl
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
  rcases hi with rfl | rfl | rfl <;>
    norm_num [σ, hr0, hr1, hr2, Equiv.swap_apply_def, Fin.ext_iff, Equiv.Perm.one_symm, Equiv.Perm.one_apply] at h ⊢ <;>
    constructor <;> nlinarith [h.1, h.2]

end OM.NNN2
