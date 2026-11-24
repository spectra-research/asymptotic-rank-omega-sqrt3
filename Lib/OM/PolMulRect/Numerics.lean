import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! # Numerical consequences of the quadratic bound in AvdBZ Proposition 4.14 -/

namespace OM.PolMulRect

/-- The quadratic bound on nonnegative weights forces the angular condition
for the rectangular spectral region, including its boundary. -/
theorem angular_of_quadratic_bound (v : Fin 3 → ℝ) (hv0 : ∀ i, 0 ≤ v i)
    (hv1 : ∀ i, v i ≤ 1)
    (hquad : ∀ x y z : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ z →
      4 * (v 0 * y * z + v 1 * x * z + v 2 * x * y) ≤ (x + y + z) ^ 2) :
    Real.pi / 2 ≤ Real.arccos (Real.sqrt (v 0)) + Real.arccos (Real.sqrt (v 1)) +
      Real.arccos (Real.sqrt (v 2)) := by
  let a (i : Fin 3) := Real.arccos (Real.sqrt (v i))
  change Real.pi / 2 ≤ a 0 + a 1 + a 2
  by_contra! hsum
  let ε := (Real.pi / 2 - (a 0 + a 1 + a 2)) / 3
  have hε : 0 < ε := div_pos (sub_pos.mpr hsum) (by norm_num)
  let b (i : Fin 3) := 2 * (a i + ε)
  have ha (i : Fin 3) : 0 ≤ a i := Real.arccos_nonneg _
  have hpos (i : Fin 3) : 0 < b i := mul_pos two_pos (add_pos_of_nonneg_of_pos (ha i) hε)
  have hπ : b 0 + b 1 + b 2 = Real.pi := by dsimp [b, ε]; ring
  have hlt (i : Fin 3) : b i < Real.pi := by
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl <;>
      linarith only [hπ, hpos 0, hpos 1, hpos 2]
  let s (i : Fin 3) := Real.sin (b i)
  have hs (i : Fin 3) : 0 < s i := Real.sin_pos_of_pos_of_lt_pi (hpos i) (hlt i)
  have hcos (i : Fin 3) : Real.cos (b i) < 2 * v i - 1 := by
    have hac : Real.cos (a i) = Real.sqrt (v i) :=
      Real.cos_arccos (by linarith [Real.sqrt_nonneg (v i)]) (Real.sqrt_le_one.mpr (hv1 i))
    calc
      Real.cos (b i) < Real.cos (2 * a i) :=
        Real.cos_lt_cos_of_nonneg_of_le_pi (mul_nonneg (by norm_num) (ha i)) (hlt i).le
          (by dsimp [b]; linarith only [hε])
      _ = 2 * v i - 1 := by rw [Real.cos_two_mul, hac, Real.sq_sqrt (hv0 i)]
  -- The sines of three angles summing to π attain equality for the cosines of those angles.
  have sine (i j k : Fin 3) (h : b i + b j + b k = Real.pi) :
      s i = s j * Real.cos (b k) + Real.cos (b j) * s k := by
    change Real.sin (b i) = Real.sin (b j) * Real.cos (b k) + Real.cos (b j) * Real.sin (b k)
    rw [← Real.sin_add, ← Real.sin_pi_sub (b i), show Real.pi - b i = b j + b k by linarith]
  have boundary : s 0 ^ 2 + s 1 ^ 2 + s 2 ^ 2 =
      2 * (Real.cos (b 0) * s 1 * s 2 + Real.cos (b 1) * s 0 * s 2 +
        Real.cos (b 2) * s 0 * s 1) := by
    linear_combination s 0 * sine 0 1 2 hπ + s 1 * sine 1 2 0 (by linarith only [hπ]) +
      s 2 * sine 2 0 1 (by linarith only [hπ])
  have strict (i j k : Fin 3) := mul_lt_mul_of_pos_right (hcos i) (mul_pos (hs j) (hs k))
  nlinarith only [hquad _ _ _ (hs 0).le (hs 1).le (hs 2).le, boundary,
    strict 0 1 2, strict 1 0 2, strict 2 0 1]

/-- The first case of AvdBZ Lemma 4.15, testing the quadratic bound at
`(a+b,b,a)`. Only the coefficient of the smallest dimension needs a sign. -/
theorem weight_le_add_of_quadratic_bound (v : Fin 3 → ℝ) (hv : 0 ≤ v 0)
    (hquad : ∀ x y z : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ z →
      4 * (v 0 * y * z + v 1 * x * z + v 2 * x * y) ≤ (x + y + z) ^ 2)
    {a b c : ℝ} (hc : 0 ≤ c) (hcb : c ≤ b) (hba : b ≤ a) (hflat : c * (a + b) ≤ a * b) :
    a * v 1 + b * v 2 + c * v 0 ≤ a + b := by
  have hb := hc.trans hcb
  have ha := hb.trans hba
  rcases (add_nonneg ha hb).lt_or_eq with h | h
  · apply le_of_mul_le_mul_left (a := a + b) _ h
    nlinarith only [hquad (a + b) b a h.le hb ha, mul_le_mul_of_nonneg_right hflat hv]
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    have hc0 : c = 0 := by linarith
    simp [ha0, hb0, hc0]

end OM.PolMulRect
