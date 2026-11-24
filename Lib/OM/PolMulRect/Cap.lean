import Lib.OM.PolMulRect.Weighted

/-! # The quadratic spectral bound

Proposition 4.14 of Amanov–van den Berg–Zuiddam, obtained by comparing the
growth rates of the weighted polynomial profiles and taking rational limits.
-/

namespace OM.PolMulRect

open OM.PolMul Foundations.PairUnitExponents

universe u
variable {F : Type u} [Field F]

/-- Telescoping from `G₁ ≥ 1` produces a lower power bound on every diagonal product. -/
theorem weightedProduct_growth (φ : Spectral F) (x : Fin 3 → ℕ+) (n : ℕ+) :
    (((n : ℝ) + 1) / 2) ^ (8 * quadraticWeight φ x / weightSum x) ≤ weightedProduct φ x n n := by
  let E : ℝ := 8 * quadraticWeight φ x / weightSum x
  induction n using PNat.recOn with
  | one =>
    simpa only [PNat.val_ofNat, Nat.cast_one, show ((1 : ℝ) + 1) / 2 = 1 by norm_num,
      Real.one_rpow] using one_le_weightedProduct φ x 1 1
  | succ n ih =>
    have hn : (0 : ℝ) < n := by positivity
    have hd : (0 : ℝ) < n + 1 := by positivity
    have hG := zero_lt_one.trans_le (one_le_weightedProduct φ x n n)
    have step := (le_div_iff₀ hG).mp (weightedProduct_step φ x n)
    calc
      _ = ((((n : ℝ) + 2) / (n + 1)) * ((n + 1) / 2)) ^ E := by
        congr 1
        push_cast
        field_simp
        ring
      _ = (((n : ℝ) + 2) / (n + 1)) ^ E * ((n + 1) / 2) ^ E :=
        Real.mul_rpow (by positivity) (by positivity)
      _ ≤ _ := (mul_le_mul_of_nonneg_left ih (Real.rpow_nonneg (by positivity) E)).trans step

/-- Proposition 4.14 for positive integral weights. A larger lower exponent
would make the quotient by the upper power grow without bound. -/
theorem quadratic_bound_int (φ : Spectral F) (x : Fin 3 → ℕ+) :
    4 * quadraticWeight φ x ≤ (weightSum x : ℝ) ^ 2 := by
  let E : ℝ := 8 * quadraticWeight φ x / weightSum x
  let K : ℕ := 2 * weightSum x
  let S : ℝ := weightSum x
  have hS : 0 < S := by dsimp [S, weightSum]; positivity
  have hE : 0 ≤ E := by
    have hp₀ := (theta_mem_Icc φ 0).1
    have hp₁ := (theta_mem_Icc φ 1).1
    have hp₂ := (theta_mem_Icc φ 2).1
    dsimp [E, quadraticWeight]
    positivity
  have power_bound (n : ℕ+) : (n : ℝ) ^ E ≤ (2 ^ E * S ^ K) * (n : ℝ) ^ K := by
    calc
      _ = (2 : ℝ) ^ E * ((n : ℝ) / 2) ^ E := by
        rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity)]
        congr 1
        ring
      _ ≤ 2 ^ E * (((n : ℝ) + 1) / 2) ^ E := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by norm_num) _)
        apply Real.rpow_le_rpow (by positivity) _ hE
        linarith
      _ ≤ 2 ^ E * ((n : ℝ) * S) ^ K := mul_le_mul_of_nonneg_left
        ((weightedProduct_growth φ x n).trans (weightedProduct_upper φ x n)) (Real.rpow_nonneg (by norm_num) _)
      _ = _ := by rw [mul_pow]; ring
  have hexp : E ≤ (K : ℝ) := by
    by_contra! h
    have hlim : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (E - (K : ℝ))) Filter.atTop Filter.atTop :=
      (tendsto_rpow_atTop (sub_pos.mpr h)).comp tendsto_natCast_atTop_atTop
    obtain ⟨n, hn, hlarge⟩ := ((Filter.eventually_ge_atTop (1 : ℕ)).and
      (hlim.eventually_gt_atTop ((2 : ℝ) ^ E * S ^ K))).exists
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    change (2 : ℝ) ^ E * S ^ K < (n : ℝ) ^ (E - (K : ℝ)) at hlarge
    rw [Real.rpow_sub hnR, Real.rpow_natCast] at hlarge
    exact (power_bound ⟨n, hn⟩).not_gt ((lt_div_iff₀ (pow_pos hnR K)).mp hlarge)
  have H := (div_le_iff₀ hS).mp hexp
  dsimp only [K, S] at H
  push_cast at H
  nlinarith only [H]

/-- After division by a common positive denominator the integer-weight
inequality still holds, since both sides have degree two. -/
private lemma quadratic_scaled {p q r : ℝ} {a b c : ℕ+} {d : ℝ} (hd : 0 < d)
    (h : 4 * (p * b * c + q * a * c + r * a * b) ≤ ((a : ℝ) + b + c) ^ 2) :
    4 * (p * (b / d) * (c / d) + q * (a / d) * (c / d) + r * (a / d) * (b / d)) ≤
      (a / d + b / d + c / d) ^ 2 := by
  convert! (div_le_div_iff_of_pos_right (sq_pos_of_pos hd)).2 h using 1 <;> ring

private noncomputable def roundedWeight (x : ℝ) (m : ℕ) : ℕ+ :=
  ⟨⌊((m : ℝ) + 1) * x⌋₊ + 1, Nat.succ_pos _⟩

private lemma roundedWeight_tendsto {x : ℝ} (hx : 0 ≤ x) :
    Filter.Tendsto (fun m : ℕ => (roundedWeight x m : ℝ) / ((m : ℝ) + 1))
      Filter.atTop (nhds x) := by
  have hu : Filter.Tendsto (fun m : ℕ => x + 1 / ((m : ℝ) + 1)) Filter.atTop (nhds x) := by
    simpa only [add_zero] using
      (tendsto_const_nhds (x := x) (f := Filter.atTop (α := ℕ))).add tendsto_one_div_add_atTop_nhds_zero_nat
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
  · intro m
    rw [le_div_iff₀ (by positivity)]
    change x * ((m : ℝ) + 1) ≤ ((⌊((m : ℝ) + 1) * x⌋₊ + 1 : ℕ) : ℝ)
    push_cast
    linarith only [Nat.lt_floor_add_one (((m : ℝ) + 1) * x)]
  · intro m
    rw [div_le_iff₀ (by positivity)]
    change ((⌊((m : ℝ) + 1) * x⌋₊ + 1 : ℕ) : ℝ) ≤ (x + 1 / ((m : ℝ) + 1)) * ((m : ℝ) + 1)
    rw [add_mul x (1 / ((m : ℝ) + 1)), div_mul_cancel₀ _ (by positivity : (m : ℝ) + 1 ≠ 0)]
    push_cast
    linarith only [Nat.floor_le (mul_nonneg (by positivity : 0 ≤ (m : ℝ) + 1) hx)]

/-- Amanov–van den Berg–Zuiddam, Proposition 4.14, in logarithmic form.
The weights may vanish on any face of the nonnegative octant. -/
theorem quadratic_bound (φ : Spectral F) (x y z : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    4 * (theta φ 0 * y * z + theta φ 1 * x * z + theta φ 2 * x * y) ≤ (x + y + z) ^ 2 := by
  have hint (a b c : ℕ+) :
      4 * (theta φ 0 * b * c + theta φ 1 * a * c + theta φ 2 * a * b) ≤
        ((a : ℝ) + b + c) ^ 2 := by
    simpa [quadraticWeight, weightSum] using quadratic_bound_int φ ![a, b, c]
  let f (w : ℝ) (m : ℕ) : ℝ := roundedWeight w m / ((m : ℝ) + 1)
  have H (m : ℕ) :
      4 * (theta φ 0 * f y m * f z m + theta φ 1 * f x m * f z m +
        theta φ 2 * f x m * f y m) ≤ (f x m + f y m + f z m) ^ 2 :=
    quadratic_scaled (by positivity) (hint (roundedWeight x m) (roundedWeight y m) (roundedWeight z m))
  have tx : Filter.Tendsto (f x) Filter.atTop (nhds x) := roundedWeight_tendsto hx
  have ty : Filter.Tendsto (f y) Filter.atTop (nhds y) := roundedWeight_tendsto hy
  have tz : Filter.Tendsto (f z) Filter.atTop (nhds z) := roundedWeight_tendsto hz
  exact le_of_tendsto_of_tendsto'
    (tendsto_const_nhds.mul ((((tendsto_const_nhds.mul ty).mul tz).add
      ((tendsto_const_nhds.mul tx).mul tz)).add ((tendsto_const_nhds.mul tx).mul ty)))
    (((tx.add ty).add tz).pow 2) H

end OM.PolMulRect
