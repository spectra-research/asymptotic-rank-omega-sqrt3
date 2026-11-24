import Lib.OM.NNN11.ValueInstances
import Lib.E.WordPower

/-! Move the spectral point together with the ordered rectangular tensor. -/
noncomputable section
namespace OM.NNN11
open CoordinateTensor OM.NNN.Raw
open Semicontinuity Foundations.HyperbolicLift Foundations.OrientationTransport
open Lib.E.RectangularSpectrum
set_option maxHeartbeats 1000000

variable {I J K : Type} [Fintype I] [Fintype J] [Fintype K]
  [Nonempty I] [Nonempty J] [Nonempty K]

lemma value_eq_cls (φ : PolMul.Spectral ℂ) (T : Tensor ℂ I J K) :
    value φ T = AsymptoticSpectrumDuality.AsymptoticSpectrum.eval _ (cls T) φ := by
  have h := value_encode φ (Lib.E.tensorToK (enumeration I) (enumeration J) (enumeration K) T)
  have he := value_reindex φ T (enumeration I) (enumeration J) (enumeration K)
  exact he.symm.trans h

theorem value_swap12 (φ : PolMul.Spectral ℂ) (T : Tensor ℂ I J K) :
    value (pullPoint φ (rot 1)) (swap12 T) = value φ T := by
  rw [value_eq_cls, cls_swap12]
  change AsymptoticSpectrumDuality.AsymptoticSpectrum.eval _
    (legPermEquiv (rot 1) (legPermEquiv (rot 1) (cls T))) φ = _
  rw [legPermEquiv_rot_rot, ← value_eq_cls]

theorem value_swap02 (φ : PolMul.Spectral ℂ) (T : Tensor ℂ I J K) :
    value (pullPoint φ (rot 0)) (swap02 T) = value φ T := by
  rw [value_eq_cls, cls_swap02]
  change AsymptoticSpectrumDuality.AsymptoticSpectrum.eval _
    (legPermEquiv (rot 0) (legPermEquiv (rot 0) (cls T))) φ = _
  rw [legPermEquiv_rot_rot, ← value_eq_cls]

end OM.NNN11
