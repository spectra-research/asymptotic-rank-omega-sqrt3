import Lib.OM.NNN11.InnerRates
import Lib.OM.NNN11.Transport

/-! The rectangular inner construction with either short party heavy. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN11
open CoordinateTensor OM.NNN.Raw
open ExtractionAB (X)
open Foundations.PairUnitExponents Foundations.OrientationTransport Lib.E.RectangularSpectrum
set_option maxHeartbeats 2000000

theorem rect_finite_C (m H : ℕ) (hcone : 5 * H ≤ m) (φ : PolMul.Spectral ℂ)
    (t : Fin 3 → ℝ) (ht : ∀ i, t i ∈ Set.Icc (1 / 4 : ℝ) 1)
    (hθ : ∀ i, theta φ i ≤ t i) (hs : t 0 + t 1 + t 2 = (9 : ℝ) / 4)
    (hh : rectHead (fun x => max 0 x) false (t 0) (t 1) (t 2) m H
      (m * innerF (t 0) - H * innerG (t 0)) ≤ 70 * (m * innerF (t 0) - H * innerG (t 0)))
    (T : Tensor ℂ (X m) (X (m - H)) (X (m - H))) :
    value φ T ≤ 2 * (2 : ℝ) ^ (m * innerF (t 0) - H * innerG (t 0)) := by
  apply network70_rounded φ t hθ (by simpa only [Fin.sum_univ_three] using! hs) _
    (rect_rates_cap m H hcone t ht hs) _ T
  rw [rect_head_eq m H (by omega) t _ hs]
  exact hh

theorem rect_finite (m H : ℕ) (hcone : 5 * H ≤ m) (φ : PolMul.Spectral ℂ)
    (t : Fin 3 → ℝ) (ht : ∀ i, t i ∈ Set.Icc (1 / 4 : ℝ) 1)
    (hθ : ∀ i, theta φ i ≤ t i) (hs : t 0 + t 1 + t 2 = (9 : ℝ) / 4)
    (T : Tensor ℂ (X m) (X (m - H)) (X (m - H))) :
    value φ T ≤ 2 * (2 : ℝ) ^ (m * innerF (t 0) - H * innerG (t 0)) := by
  obtain ⟨h, hh⟩ := exists_rect_head (ht 0) (ht 1) (ht 2) hs (Nat.cast_nonneg m) (Nat.cast_nonneg H)
  cases h with
  | false => exact rect_finite_C m H hcone φ t ht hθ hs hh T
  | true =>
    let ψ := pullPoint φ (rot 1)
    let v : Fin 3 → ℝ := ![t 0, t 2, t 1]
    have hv (i) : v i ∈ Set.Icc (1 / 4 : ℝ) 1 := by
      fin_cases i <;> first | exact ht 0 | exact ht 2 | exact ht 1
    have hvθ (i) : theta ψ i ≤ v i := by
      rw [theta_legReindex]
      fin_cases i <;> first | exact hθ 0 | exact hθ 2 | exact hθ 1
    have hvsum : v 0 + v 1 + v 2 = (9 : ℝ) / 4 := by change t 0 + t 2 + t 1 = _; linarith
    have hvhead : rectHead (fun x => max 0 x) false (v 0) (v 1) (v 2) m H
        (m * innerF (v 0) - H * innerG (v 0)) ≤ 70 * (m * innerF (v 0) - H * innerG (v 0)) := by
      have he : rectHead (fun x => max 0 x) false (v 0) (v 1) (v 2) m H
          (m * innerF (v 0) - H * innerG (v 0)) =
          rectHead (fun x => max 0 x) true (t 0) (t 1) (t 2) m H
          (m * innerF (t 0) - H * innerG (t 0)) := by
        dsimp [v, rectHead]
        ring
      rw [he]
      exact hh
    have hb := rect_finite_C m H hcone ψ v hv hvθ hvsum hvhead (swap12 T)
    rw [value_swap12] at hb
    exact hb

end OM.NNN11
