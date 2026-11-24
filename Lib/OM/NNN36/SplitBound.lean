import PLATFORM.Statements.«R115.2»
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring


/-! # The hypothesis of Theorem 1.3(iii) without coordinates

If the longest side `c` is split as `p + q` with `c (p a² + q b²) ≤ p q (p q + c²)`, then the root of the cubic
satisfies the coordinate form of the hypothesis. -/

namespace P2M.R115

theorem apex_bound_of_pq (a b c : ℝ) (h0 : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hc : c < a + b)
    (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = c)
    (h : c * (p * a ^ 2 + q * b ^ 2) ≤ p * q * (p * q + c ^ 2))
    (x : ℝ) (hx : x ∈ Set.Ioo 0 1) (hroot : 3 * x ^ 2 - 2 * x ^ 3 = (normalizedApex a b c).re) :
    (x - (normalizedApex a b c).re) ^ 2 + (normalizedApex a b c).im ^ 2 ≤ x ^ 2 * (1 - x) ^ 2 := by
  let ξ := (b ^ 2 + c ^ 2 - a ^ 2) / (2 * c ^ 2)
  change 3 * x ^ 2 - 2 * x ^ 3 = ξ at hroot
  change (x - ξ) ^ 2 + (Real.sqrt ((b / c) ^ 2 - ξ ^ 2)) ^ 2 ≤ _
  have hc0 : 0 < c := by linarith
  have hb0 := h0.trans hab
  have hξ : 0 ≤ ξ := by
    refine div_nonneg ?_ (by positivity)
    linarith only [(sq_le_sq₀ h0 hb0).2 hab, sq_nonneg c]
  have hξb : ξ ≤ b / c := by
    dsimp [ξ]
    rw [div_le_div_iff₀ (by positivity) hc0]
    have hd : (c - b) ^ 2 ≤ a ^ 2 :=
      (sq_le_sq₀ (sub_nonneg.mpr hbc) h0).2 (by linarith)
    nlinarith only [mul_nonneg (sub_nonneg.mpr hd) hc0.le]
  rw [Real.sq_sqrt (sub_nonneg.mpr ((sq_le_sq₀ hξ (div_nonneg hb0 hc0.le)).2 hξb))]
  let s := p / c
  have hs : 0 ≤ s := div_nonneg hp hc0.le
  have hs1 : s ≤ 1 := (div_le_one hc0).2 (by linarith)
  -- Stewart's identity at the point s on the normalized base.
  have hbase : (s - ξ) ^ 2 + ((b / c) ^ 2 - ξ ^ 2) - s ^ 2 * (1 - s) ^ 2 ≤ 0 := calc
    _ = (c * (p * a ^ 2 + q * b ^ 2) - p * q * (p * q + c ^ 2)) / c ^ 4 := by
      rw [show q = c - p by linarith]
      dsimp [s, ξ]
      field_simp [hc0.ne']
      ring
    _ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h) (by positivity)
  -- At a cubic root, the difference of the two quartic values has a square factor.
  have hmin : (x - ξ) ^ 2 - x ^ 2 * (1 - x) ^ 2 ≤ (s - ξ) ^ 2 - s ^ 2 * (1 - s) ^ 2 := by
    rw [← sub_nonneg, ← hroot]
    have hx0 := hx.1.le
    have hx1 := sub_nonneg.mpr hx.2.le
    have hs' := sub_nonneg.mpr hs1
    calc
      0 ≤ (s - x) ^ 2 * (s * (1 - s) + s * (1 - x) + x * (1 - s) + 3 * x * (1 - x)) := by
        positivity
      _ = _ := by ring
  linarith only [hbase, hmin]

end P2M.R115
