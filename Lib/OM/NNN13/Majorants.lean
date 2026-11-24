import Lib.OM.NNN13.AffineExtraction
import Lib.OM.NNN12.Powers

/-! Connect the six affine candidate prices to the finite all-shape excess.
The affine bounds used here are already valid before any recursive step.
The last theorem states the remaining uniform finite-step premise explicitly. -/
noncomputable section
namespace OM.NNN13
open CoordinateTensor OM.NNN.Raw
open NNN12 (Shape DyadicTensor volume excess)

lemma plane_add_constant (c x : Fin 3 → ℝ) (s : ℝ) :
    plane (fun i => c i + s) x = plane c x + s * (x 0 + x 1 + x 2) := by
  unfold plane
  ring

lemma potential_le_candidate (r z : ℝ) (x : Fin 3 → ℝ) (i : Fin 3) :
    potential r z x ≤ plane (fun j => candidateCoefficients r z i j + lift) x := by
  rw [plane_add_constant, potential]
  exact add_le_add (basePotential_le_candidate r z x i) le_rfl

lemma potential_le_star (r z : ℝ) (x : Fin 3 → ℝ) (i : Fin 3) :
    potential r z x ≤ plane (fun j => starCoefficients (profile r z) i j + lift) x := by
  rw [plane_add_constant, potential]
  exact add_le_add ((min_le_left _ _).trans (min3_le _ i)) le_rfl

theorem candidate_affineBound_with_error (φ : PolMul.Spectral ℂ) (r z ε : ℝ)
    (hb : ∀ (v : Shape) (U : DyadicTensor v),
      value φ U ≤ (2 : ℝ) ^ (target r z v + ε * volume v)) (i : Fin 3) :
    AffineBound φ (fun j => candidateCoefficients r z i j + lift + ε) := by
  apply affineBound_of_majorant φ hb
  intro v
  rw [plane_add_constant]
  exact add_le_add (potential_le_candidate r z (fun j => (v j : ℝ)) i) le_rfl

theorem star_affineBound_with_error (φ : PolMul.Spectral ℂ) (r z ε : ℝ)
    (hb : ∀ (v : Shape) (U : DyadicTensor v),
      value φ U ≤ (2 : ℝ) ^ (target r z v + ε * volume v)) (i : Fin 3) :
    AffineBound φ (fun j => starCoefficients (profile r z) i j + lift + ε) := by
  apply affineBound_of_majorant φ hb
  intro v
  rw [plane_add_constant]
  exact add_le_add (potential_le_star r z (fun j => (v j : ℝ)) i) le_rfl

/-- All three recursive planes majorize actual tensor values with the
finite worst-excess term; no desired invariant is assumed. -/
theorem candidate_affineBound_at_excess (φ : PolMul.Spectral ℂ) {r z : ℝ}
    (hr : r ∈ Set.Icc 0 radius) (hz : z ∈ Set.Icc 0 r) (i : Fin 3) :
    AffineBound φ (fun j => candidateCoefficients r z i j + lift + excess φ (target r z)) :=
  candidate_affineBound_with_error φ r z _ (NNN12.value_le_excess φ (target_nonneg hr hz)) i

theorem star_affineBound_at_excess (φ : PolMul.Spectral ℂ) {r z : ℝ}
    (hr : r ∈ Set.Icc 0 radius) (hz : z ∈ Set.Icc 0 r) (i : Fin 3) :
    AffineBound φ (fun j => starCoefficients (profile r z) i j + lift + excess φ (target r z)) :=
  star_affineBound_with_error φ r z _ (NNN12.value_le_excess φ (target_nonneg hr hz)) i

lemma target_power (r z : ℝ) (q : ℕ) (v : Shape) :
    target r z (NNN12.powerShape q v) = q * target r z v := by
  simp only [target, NNN12.powerShape, Nat.cast_mul]
  exact potential_scale r z _ (Nat.cast_nonneg q)

/-- Powers remove every shape-independent finite loss before the excess
supremum is taken. Only the finite network certificate remains a premise. -/
theorem invariant_of_finite_step (φ : PolMul.Spectral ℂ) {r z : ℝ}
    (hr : r ∈ Set.Icc 0 radius) (hz : z ∈ Set.Icc 0 r)
    (step : ∀ ε : ℝ, 0 ≤ ε →
      (∀ (v : Shape) (U : DyadicTensor v), value φ U ≤ (2 : ℝ) ^ (target r z v + ε * volume v)) →
      ∃ C : ℝ, ∀ (v : Shape) (U : DyadicTensor v),
        value φ U ≤ C * (2 : ℝ) ^ (target r z v + gamma * ε * volume v))
    (v : Shape) (U : DyadicTensor v) : value φ U ≤ (2 : ℝ) ^ target r z v := by
  apply invariant_of_combined_step φ (target_nonneg hr hz) _ v U
  intro ε hε hb
  obtain ⟨C, hC⟩ := step ε hε hb
  apply NNN12.remove_uniform_constant φ (C := C) (hb := hC)
  intro q v
  rw [target_power, NNN12.volume_power]
  ring

end OM.NNN13
