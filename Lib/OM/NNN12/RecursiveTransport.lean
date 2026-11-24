import Lib.OM.NNN12.Powers
import Lib.OM.NNN11.Transport

/-! Exact covariance of the all-format recursive hypothesis. The tensor and
point move together, and the numerical sorted potential is invariant. -/
noncomputable section
namespace OM.NNN12
open CoordinateTensor OM.NNN.Raw
open Foundations.OrientationTransport Lib.E.RectangularSpectrum
set_option maxHeartbeats 1500000

def swap12Shape (v : Shape) : Shape := ![v 0, v 2, v 1]
def swap02Shape (v : Shape) : Shape := ![v 2, v 1, v 0]

lemma fallback_swap12 (x y z : ℝ) : fallbackPotential x z y = fallbackPotential x y z := by
  have hh : largest x z y = largest x y z := by unfold largest; ac_rfl
  have hl : smallest x z y = smallest x y z := by unfold smallest; ac_rfl
  simp only [fallbackPotential, potential, affine, middle, hh, hl]
  congr 2 <;> ring

lemma fallback_swap02 (x y z : ℝ) : fallbackPotential z y x = fallbackPotential x y z := by
  have hh : largest z y x = largest x y z := by unfold largest; ac_rfl
  have hl : smallest z y x = smallest x y z := by unfold smallest; ac_rfl
  simp only [fallbackPotential, potential, affine, middle, hh, hl]
  congr 2 <;> ring

lemma target_swap12 (v : Shape) : target (swap12Shape v) = target v := fallback_swap12 _ _ _
lemma target_swap02 (v : Shape) : target (swap02Shape v) = target v := fallback_swap02 _ _ _
lemma volume_swap12 (v : Shape) : volume (swap12Shape v) = volume v := by
  change (v 0 : ℝ) + v 2 + v 1 = (v 0 : ℝ) + v 1 + v 2
  ring
lemma volume_swap02 (v : Shape) : volume (swap02Shape v) = volume v := by
  change (v 2 : ℝ) + v 1 + v 0 = (v 0 : ℝ) + v 1 + v 2
  ring

theorem bound_swap12 (φ : PolMul.Spectral ℂ) (ε : ℝ)
    (hb : ∀ (v : Shape) (U : DyadicTensor v), value φ U ≤ (2 : ℝ) ^ (target v + ε * volume v)) :
    ∀ (v : Shape) (U : DyadicTensor v),
      value (pullPoint φ (rot 1)) U ≤ (2 : ℝ) ^ (target v + ε * volume v) := by
  intro v U
  have hh := hb (swap12Shape v) (swap12 U)
  have he := NNN11.value_swap12 φ (swap12 U)
  change value (pullPoint φ (rot 1)) U = value φ (swap12 U) at he
  rw [target_swap12, volume_swap12, ← he] at hh
  exact hh

theorem bound_swap02 (φ : PolMul.Spectral ℂ) (ε : ℝ)
    (hb : ∀ (v : Shape) (U : DyadicTensor v), value φ U ≤ (2 : ℝ) ^ (target v + ε * volume v)) :
    ∀ (v : Shape) (U : DyadicTensor v),
      value (pullPoint φ (rot 0)) U ≤ (2 : ℝ) ^ (target v + ε * volume v) := by
  intro v U
  have hh := hb (swap02Shape v) (swap02 U)
  have he := NNN11.value_swap02 φ (swap02 U)
  change value (pullPoint φ (rot 0)) U = value φ (swap02 U) at he
  rw [target_swap02, volume_swap02, ← he] at hh
  exact hh

end OM.NNN12
