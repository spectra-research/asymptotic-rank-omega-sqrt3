import Lib.OM.NNN12.Geometry

noncomputable section
namespace OM.NNN12

def logMoment19 (D : ℝ) : ℝ :=
  Real.logb 2 (1 + 18 * (2 : ℝ) ^ (5 * D)) - Real.logb 2 19
def middleMoment (t x y z : ℝ) : ℝ :=
  196 * (b * x + a * y + c * z) + 7 * z * logMoment19 (t - b - c)
def shortMomentA (t x y z : ℝ) : ℝ :=
  196 * affine x y z + 196 * eta * (y - z) + 7 * y * logMoment19 (t - a - b - eta)
def shortMomentC (t x y z : ℝ) : ℝ :=
  196 * (b * x + c * y + a * z) + 7 * y * logMoment19 (t - b - c)
def denominator (t : ℝ) : ℝ := 196 * (1 + 9 / 4) - 70 * t
def contraction (t₀ t₁ t₂ : ℝ) : ℝ := 196 * (t₁ + t₂) / denominator t₀

lemma logMoment19_ratio (D : ℝ) :
    logMoment19 D = Real.logb 2 ((1 + 18 * (2 : ℝ) ^ (5 * D)) / 19) := by
  rw [Real.logb_div (by positivity) (by norm_num)]
  rfl

lemma logMoment19_capacity (D : ℝ) : -Real.logb 2 19 ≤ logMoment19 D := by
  have h : 0 ≤ Real.logb 2 (1 + 18 * (2 : ℝ) ^ (5 * D)) := by
    have hh := (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 1) (by positivity)).2
        (show (1 : ℝ) ≤ 1 + 18 * (2 : ℝ) ^ (5 * D) from le_add_of_nonneg_right (by positivity))
    simpa using! hh
  dsimp [logMoment19]
  linarith

lemma shortMoment_difference (t x y z : ℝ) :
    shortMomentC t x y z - shortMomentA t x y z = 196 * (b - a) * (x - y) := by
  have he : t - a - b - eta = t - b - c := by dsimp [a, b, c, eta]; ring
  simp only [shortMomentC, shortMomentA, he, affine]
  dsimp [a, b, c, eta]
  ring

lemma shortMomentA_le_C (t : ℝ) {x y z : ℝ} (hxy : y ≤ x) :
    shortMomentA t x y z ≤ shortMomentC t x y z := by
  have hh := mul_nonneg (show 0 ≤ 196 * (b - a) by norm_num [a, b]) (sub_nonneg.mpr hxy)
  rw [← shortMoment_difference t x y z] at hh
  linarith

lemma middleMoment_capacity (t : ℝ) {x y z : ℝ} (hxy : y ≤ x) (hz : 0 ≤ z) :
    196 * affine x y z ≤ middleMoment t x y z + 7 * z * Real.logb 2 19 := by
  have hl := mul_le_mul_of_nonneg_left (logMoment19_capacity (t - b - c))
    (show 0 ≤ 7 * z by positivity)
  have hs := mul_nonneg (show 0 ≤ b - a by norm_num [a, b]) (sub_nonneg.mpr hxy)
  dsimp [affine, middleMoment]
  nlinarith

lemma shortMomentA_capacity (t : ℝ) {x y z : ℝ} (hyz : z ≤ y) (hy : 0 ≤ y) :
    196 * affine x y z ≤ shortMomentA t x y z + 7 * y * Real.logb 2 19 := by
  have hl := mul_le_mul_of_nonneg_left (logMoment19_capacity (t - a - b - eta))
    (show 0 ≤ 7 * y by positivity)
  have hs := mul_nonneg (show 0 ≤ eta by norm_num [eta]) (sub_nonneg.mpr hyz)
  dsimp [shortMomentA]
  nlinarith

lemma denominator_pos {t : ℝ} (ht : t ≤ 1) : 0 < denominator t := by
  dsimp [denominator]
  linarith

/-- The error factor is uniform even when the longest party changes. -/
theorem contraction_le_gamma {t₀ t₁ t₂ : ℝ} (h₀ : 0 ≤ t₀) (h₀' : t₀ ≤ 1)
    (hs : t₀ + t₁ + t₂ = 9 / 4) : contraction t₀ t₁ t₂ ≤ gamma := by
  apply (div_le_iff₀ (denominator_pos h₀')).2
  dsimp [denominator, gamma]
  linarith

/-- A sharper bound from the same scalar inequality, for the scalar bound. -/
theorem contraction_le_near {t₀ t₁ t₂ : ℝ} (h₀ : lower ≤ t₀) (h₀' : t₀ ≤ upper)
    (hs : t₀ + t₁ + t₂ = 9 / 4) : contraction t₀ t₁ t₂ ≤ 52668 / 104435 := by
  have ht : t₀ ≤ 1 := by dsimp [upper] at h₀'; linarith
  apply (div_le_iff₀ (denominator_pos ht)).2
  dsimp [denominator, lower] at *
  linarith

lemma residual_error {ε V E : ℝ} (hε : 0 ≤ ε) (hE : 0 ≤ E) :
    ε * (196 * V - 2 * E) ≤ 196 * ε * V := by
  nlinarith [mul_nonneg hε hE]

/-- The target increase pays for both full-group errors, keeping the last
group's actual retained tensor factor out of the recursion. -/
theorem error_payment {t₀ t₁ t₂ ε V : ℝ} (h₀ : 0 ≤ t₀) (h₀' : t₀ ≤ 1)
    (hs : t₀ + t₁ + t₂ = 9 / 4) (hε : 0 ≤ ε) (hV : 0 ≤ V) :
    196 * (t₁ + t₂) * ε * V ≤ denominator t₀ * gamma * ε * V := by
  have hh := (div_le_iff₀ (denominator_pos h₀')).1 (contraction_le_gamma h₀ h₀' hs)
  nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh hε) hV]

/-- Full-group rates never overflow their zero-error capacity. -/
theorem full_rate_cap {P M C ε V : ℝ} (hC : 0 ≤ C) (hcap : 196 * P ≤ M + C)
    (hε : 0 ≤ ε) (hV : 0 ≤ V) :
    max 0 (196 * (P + gamma * ε * V) - (M + 196 * ε * V)) ≤ C := by
  apply max_le hC
  have he := mul_nonneg hε hV
  dsimp [gamma]
  nlinarith

/-- Only the retained raw group needs an overflow fallback, and it uses
the raw star rather than an assumed recursive invariant. -/
theorem raw_rate_overflow {m A S K C : ℝ} (hm : 0 < m) (hC : 0 ≤ C) (hK : K ≤ C)
    (ho : C < max 0 (m * A - (m * S - K))) : S < A := by
  have hh : C < m * A - (m * S - K) := (lt_max_iff.mp ho).resolve_left (not_lt.mpr hC)
  nlinarith

/-- Clipping nonnegative-weighted rates can only reduce the head cost. -/
lemma clipped_head_le {t₀ t₁ t₂ : ℝ} (h₀ : 0 ≤ t₀) (h₁ : 0 ≤ t₁) (h₂ : 0 ≤ t₂)
    (H r₀ r₁ r₂ : ℝ) :
    H - t₀ * max 0 r₀ - t₁ * max 0 r₁ - t₂ * max 0 r₂ ≤ H - t₀ * r₀ - t₁ * r₁ - t₂ * r₂ := by
  linarith [mul_le_mul_of_nonneg_left (le_max_right 0 r₀) h₀,
    mul_le_mul_of_nonneg_left (le_max_right 0 r₁) h₁,
    mul_le_mul_of_nonneg_left (le_max_right 0 r₂) h₂]

/-- Affordability algebra after adding the residual excess to both moments. -/
theorem recursive_head_affordable {t₀ t₁ t₂ P M₁ M₂ Q H ε V : ℝ}
    (h₀ : 0 ≤ t₀) (h₀' : t₀ ≤ 1) (h₁ : 0 ≤ t₁) (h₂ : 0 ≤ t₂)
    (hs : t₀ + t₁ + t₂ = 9 / 4) (hε : 0 ≤ ε) (hV : 0 ≤ V)
    (hsuper : H + t₁ * M₁ + t₂ * M₂ + t₀ * Q ≤ denominator t₀ * P) :
    H - t₀ * max 0 (126 * (P + gamma * ε * V) - Q) -
      t₁ * max 0 (196 * (P + gamma * ε * V) - (M₁ + 196 * ε * V)) -
      t₂ * max 0 (196 * (P + gamma * ε * V) - (M₂ + 196 * ε * V)) ≤
        196 * (P + gamma * ε * V) := by
  apply (clipped_head_le h₀ h₁ h₂ _ _ _ _).trans
  have hp := error_payment h₀ h₀' hs hε hV
  have he : 126 * t₀ + 196 * t₁ + 196 * t₂ + 196 = denominator t₀ := by
    dsimp [denominator]
    linarith
  have heP := congrArg (fun d : ℝ => d * (P + gamma * ε * V)) he
  nlinarith only [heP, hp, hsuper]

end OM.NNN12
