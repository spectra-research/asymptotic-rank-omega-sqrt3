import Mathlib

/-!
# Affine bounds on the spectral triangle -/

namespace OM.NNN18

theorem tri_affine_le {α β γ c R d y : ℝ} (hR : 0 < R) (hd₁ : -2 * R ≤ d) (hd₂ : d ≤ R)
    (hy₁ : -(d + 2 * R) ≤ y) (hy₂ : y ≤ d + 2 * R)
    (h1 : α + β * (-2 * R) + γ * 0 ≤ c) (h2 : α + β * R + γ * (3 * R) ≤ c)
    (h3 : α + β * R + γ * (-3 * R) ≤ c) : α + β * d + γ * y ≤ c := by
  have key : 6 * R * (α + β * d + γ * y - c) =
      2 * (R - d) * (α + β * (-2 * R) + γ * 0 - c) + (d + 2 * R + y) * (α + β * R + γ * (3 * R) - c)
        + (d + 2 * R - y) * (α + β * R + γ * (-3 * R) - c) := by ring
  have t1 := mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ 2 * (R - d)) (by linarith : α + β * (-2 * R) + γ * 0 - c ≤ 0)
  have t2 := mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ d + 2 * R + y) (by linarith : α + β * R + γ * (3 * R) - c ≤ 0)
  have t3 := mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ d + 2 * R - y) (by linarith : α + β * R + γ * (-3 * R) - c ≤ 0)
  have : 6 * R * (α + β * d + γ * y - c) ≤ 0 := by rw [key]; linarith
  have h6 : 0 < 6 * R := by linarith
  nlinarith

theorem tri_affine_ge {α β γ c R d y : ℝ} (hR : 0 < R) (hd₁ : -2 * R ≤ d) (hd₂ : d ≤ R)
    (hy₁ : -(d + 2 * R) ≤ y) (hy₂ : y ≤ d + 2 * R)
    (h1 : c ≤ α + β * (-2 * R) + γ * 0) (h2 : c ≤ α + β * R + γ * (3 * R))
    (h3 : c ≤ α + β * R + γ * (-3 * R)) : c ≤ α + β * d + γ * y := by
  have := tri_affine_le (α := -α) (β := -β) (γ := -γ) (c := -c) hR hd₁ hd₂ hy₁ hy₂
    (by linarith) (by linarith) (by linarith)
  linarith

lemma forall_fin3 {p : Fin 3 → Prop} (h0 : p 0) (h1 : p 1) (h2 : p 2) : ∀ i, p i := by
  intro i; fin_cases i
  · exact h0
  · exact h1
  · exact h2

end OM.NNN18
