import Lib.OM.NNN12.Excess
import Lib.OM.NNN10.Optimization
import Lib.OM.Omega

/-! Unconditional spectral parameter enlargement, using the proved published
omega bound, and exact coverage of the near/far parameter domains. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN12
open CoordinateTensor OM.NNN.Raw OM.NNN2 Foundations.PairUnitExponents

/-- No matrix multiplication bound is assumed: it is an imported theorem. -/
theorem exists_spectral_parameters (φ : PolMul.Spectral ℂ) :
    ∃ t : Fin 3 → ℝ, (∀ i, theta φ i ≤ t i) ∧
      (∀ i, t i ∈ Set.Icc (1 / 4 : ℝ) 1) ∧ t 0 + t 1 + t 2 = 9 / 4 := by
  obtain ⟨t, hθ, ht, hs⟩ := NNN10.exists_enlargement (theta φ) (theta_mem_Icc φ)
    (by simpa only [Fin.sum_univ_three] using! Omega.theta_sum_le_nine_quarters φ)
  exact ⟨t, hθ, ht, by simpa only [Fin.sum_univ_three] using! hs⟩

/-- The wedge parameterization follows from numerical ordering alone. It
does not permute a tensor while keeping its spectral point unchanged. -/
theorem exists_wedge {t₀ t₁ t₂ : ℝ} (hs : t₀ + t₁ + t₂ = 9 / 4)
    (h₁ : t₁ ≤ t₀) (h₂ : t₂ ≤ t₁) (h₀ : t₀ ≤ 17 / 20) :
    ∃ r s : ℝ, r ∈ Set.Icc 0 (1 / 10) ∧ s ∈ Set.Icc 0 1 ∧
      t₀ = 3 / 4 + r ∧ t₁ = 3 / 4 - r / 2 + 3 * r * s / 2 ∧
      t₂ = 3 / 4 - r / 2 - 3 * r * s / 2 := by
  let r := t₀ - 3 / 4
  have hr : r ∈ Set.Icc 0 (1 / 10) := by dsimp [r]; constructor <;> linarith
  by_cases hz : r = 0
  · refine ⟨0, 0, by norm_num, by norm_num, ?_, ?_, ?_⟩
    all_goals dsimp [r] at hz; linarith
  · have hr0 : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm hz)
    let s := (t₁ - t₂) / (3 * r)
    have hs0 : 0 ≤ s := div_nonneg (sub_nonneg.mpr h₂) (by positivity)
    have hs1 : s ≤ 1 := by
      apply (div_le_one (by positivity : (0 : ℝ) < 3 * r)).2
      dsimp [r]
      linarith
    have hprod : s * (3 * r) = t₁ - t₂ := div_mul_cancel₀ _ (by positivity : 3 * r ≠ 0)
    refine ⟨r, s, hr, ⟨hs0, hs1⟩, ?_, ?_, ?_⟩
    all_goals dsimp [r] at *; nlinarith

lemma wedge_near_iff {t r : ℝ} (h : t = 3 / 4 + r) :
    t ≤ upper ↔ r ≤ 3 / 1250 := by dsimp [upper]; rw [h]; constructor <;> intro hh <;> linarith

lemma star_region {t : ℝ} (ht : 17 / 20 ≤ t) : 9 / 4 - t ≤ 7 / 5 ∧ (7 / 5 : ℝ) < alpha := by
  constructor
  · linarith
  · norm_num [alpha]

end OM.NNN12
