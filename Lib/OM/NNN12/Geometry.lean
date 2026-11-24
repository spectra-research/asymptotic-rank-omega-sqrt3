import Lib.OM.NNN12.Potential

/-! Analytic reduction of the entire ordered active cone to its three rays.
No dimension grid and no lower bound on the shortest side are required. -/
noncomputable section
namespace OM.NNN12

def delta : ℝ := 2 * upper - alpha
def gapCoefficient : ℝ := a + b - upper
def vertexLong : ℝ := 1031221 / 836693
def vertexPair : ℝ := 271317 / 174053

lemma geometry_constants : 0 < delta ∧ 0 < gapCoefficient ∧
    vertexLong = 1 + delta / a ∧ vertexPair = 1 + delta / gapCoefficient := by
  norm_num [delta, gapCoefficient, vertexLong, vertexPair, a, b, upper, alpha]

lemma active_iff {x y z : ℝ} : affine x y z ≤ upper * (y + z) ↔
    a * (x - y) + gapCoefficient * (y - z) ≤ delta * z := by
  dsimp [affine, gapCoefficient, delta, a, b, c, upper, alpha]
  constructor <;> intro h <;> linarith

lemma active_scalar {x y : ℝ} (hxy : y ≤ x) (hy : 0 ≤ y)
    (ha : affine x y 0 ≤ upper * y) : x = 0 ∧ y = 0 := by
  dsimp [affine, a, b, c, upper] at ha
  constructor <;> linarith

/-- Homogeneous barycentric coordinates, valid also at the origin. -/
theorem active_decomposition {x y z : ℝ} (hxy : y ≤ x) (hyz : z ≤ y)
    (ha : affine x y z ≤ upper * (y + z)) :
    ∃ w₁ w₂ w₃ : ℝ, 0 ≤ w₁ ∧ 0 ≤ w₂ ∧ 0 ≤ w₃ ∧
      x = w₁ + w₂ * vertexLong + w₃ * vertexPair ∧
      y = w₁ + w₂ + w₃ * vertexPair ∧ z = w₁ + w₂ + w₃ := by
  let w₂ := a * (x - y) / delta
  let w₃ := gapCoefficient * (y - z) / delta
  have hδ := geometry_constants.1
  have hw₂ : 0 ≤ w₂ := div_nonneg (mul_nonneg (by norm_num [a]) (sub_nonneg.mpr hxy)) hδ.le
  have hw₃ : 0 ≤ w₃ := div_nonneg
    (mul_nonneg geometry_constants.2.1.le (sub_nonneg.mpr hyz)) hδ.le
  have hsum : w₂ + w₃ ≤ z := by
    rw [← add_div, div_le_iff₀ hδ]
    simpa [mul_comm] using! active_iff.mp ha
  refine ⟨z - w₂ - w₃, w₂, w₃, by linarith, hw₂, hw₃, ?_, ?_, by ring⟩
  all_goals
    dsimp [w₂, w₃, vertexLong, vertexPair, a, gapCoefficient, b, upper, delta, alpha]
    ring

/-- Any linear price gap nonnegative at the three vertices is nonnegative
on every active ordered rectangular shape. -/
theorem linear_nonneg_on_active {A B C x y z : ℝ}
    (h₁ : 0 ≤ A + B + C)
    (h₂ : 0 ≤ A * vertexLong + B + C)
    (h₃ : 0 ≤ A * vertexPair + B * vertexPair + C)
    (hxy : y ≤ x) (hyz : z ≤ y) (ha : affine x y z ≤ upper * (y + z)) :
    0 ≤ A * x + B * y + C * z := by
  obtain ⟨w₁, w₂, w₃, hw₁, hw₂, hw₃, hx, hy, hz⟩ := active_decomposition hxy hyz ha
  rw [hx, hy, hz]
  have hh : A * (w₁ + w₂ * vertexLong + w₃ * vertexPair) +
      B * (w₁ + w₂ + w₃ * vertexPair) + C * (w₁ + w₂ + w₃) =
      w₁ * (A + B + C) + w₂ * (A * vertexLong + B + C) +
        w₃ * (A * vertexPair + B * vertexPair + C) := by ring
  rw [hh]
  exact add_nonneg (add_nonneg (mul_nonneg hw₁ h₁) (mul_nonneg hw₂ h₂)) (mul_nonneg hw₃ h₃)

/-- Every near-balanced profile is in the exact box used by the analytic
certificate; no ordering of its coordinates is assumed. -/
lemma near_profile_box {t₀ t₁ t₂ : ℝ} (hs : t₀ + t₁ + t₂ = 9 / 4)
    (h₀ : t₀ ≤ upper) (h₁ : t₁ ≤ upper) (h₂ : t₂ ≤ upper) :
    t₀ ∈ Set.Icc lower upper ∧ t₁ ∈ Set.Icc lower upper ∧ t₂ ∈ Set.Icc lower upper := by
  dsimp [lower, upper] at *
  exact ⟨⟨by linarith, h₀⟩, ⟨by linarith, h₁⟩, ⟨by linarith, h₂⟩⟩

/-- The two positive transfer directions generate every admissible profile. -/
lemma near_profile_transfers {t₀ t₁ t₂ : ℝ} (hs : t₀ + t₁ + t₂ = 9 / 4)
    (h₁ : t₁ ≤ upper) (h₂ : t₂ ≤ upper) :
    0 ≤ upper - t₁ ∧ 0 ≤ upper - t₂ ∧
      t₀ = lower + (upper - t₁) + (upper - t₂) := by
  refine ⟨sub_nonneg.mpr h₁, sub_nonneg.mpr h₂, ?_⟩
  dsimp [lower, upper]
  linarith

end OM.NNN12
