import Lib.OM.PolMulRect.Cap
import Lib.OM.PolMulRect.Numerics
import Lib.OM.NNN22.F
import PLATFORM.Statements.«R88.8»

/-! # The rectangular spectral region (R88.8)

Apply the quadratic inequality of Amanov, van den Berg and Zuiddam,
Proposition 4.14, then pass from its angular form to the radical inequality.
-/

noncomputable section
namespace OM.NNN22

open Foundations.PairUnitExponents

lemma sin_sq_sum_boundary {a b c : ℝ} (h : a + b + c = Real.pi / 2) :
    Real.sin a ^ 2 + Real.sin b ^ 2 + Real.sin c ^ 2 +
      2 * (Real.sin a * Real.sin b * Real.sin c) = 1 := by
  have hc : c = Real.pi / 2 - (a + b) := by linarith
  rw [hc, Real.sin_pi_div_two_sub, Real.cos_add]
  linear_combination Real.cos b ^ 2 * Real.sin_sq_add_cos_sq a +
    (1 - Real.sin a ^ 2) * Real.sin_sq_add_cos_sq b

lemma angular_rectangular (v : Fin 3 → ℝ) (hv0 : ∀ i, 0 ≤ v i) (hv1 : ∀ i, v i ≤ 1)
    (hang : Real.pi / 2 ≤ Real.arccos (Real.sqrt (v 0)) + Real.arccos (Real.sqrt (v 1)) +
      Real.arccos (Real.sqrt (v 2))) :
    v 0 + v 1 + v 2 ≤ 2 + 2 * Real.sqrt ((1 - v 0) * (1 - v 1) * (1 - v 2)) := by
  let a : Fin 3 → ℝ := fun i => Real.arccos (Real.sqrt (v i))
  let H : ℝ := a 0 + a 1 + a 2
  have hH : Real.pi / 2 ≤ H := by simpa [H, a] using hang
  have hHpos : 0 < H := (by positivity : (0 : ℝ) < Real.pi / 2).trans_le hH
  let l : ℝ := (Real.pi / 2) / H
  let b : Fin 3 → ℝ := fun i => l * a i
  have hl0 : 0 ≤ l := div_nonneg (by positivity) hHpos.le
  have hl1 : l ≤ 1 := (div_le_one hHpos).2 hH
  have ha0 (i : Fin 3) : 0 ≤ a i := Real.arccos_nonneg _
  have ha2 (i : Fin 3) : a i ≤ Real.pi / 2 := by
    have h := Real.arccos_le_arccos (Real.sqrt_nonneg (v i))
    simpa [a] using h
  have hb0 (i : Fin 3) : 0 ≤ b i := mul_nonneg hl0 (ha0 i)
  have hb_le (i : Fin 3) : b i ≤ a i := by
    dsimp [b]
    calc
      l * a i ≤ 1 * a i := mul_le_mul_of_nonneg_right hl1 (ha0 i)
      _ = a i := one_mul _
  have hb_sum : b 0 + b 1 + b 2 = Real.pi / 2 := by
    calc
      b 0 + b 1 + b 2 = l * (a 0 + a 1 + a 2) := by dsimp [b]; ring
      _ = l * H := by rfl
      _ = Real.pi / 2 := div_mul_cancel₀ _ hHpos.ne'
  have hcos (i : Fin 3) : Real.cos (a i) = Real.sqrt (v i) := by
    exact Real.cos_arccos (by linarith [Real.sqrt_nonneg (v i)])
      (Real.sqrt_le_one.mpr (hv1 i))
  have hvia (i : Fin 3) : Real.sin (a i) ^ 2 = 1 - v i := by
    have h := Real.sin_sq_add_cos_sq (a i)
    rw [hcos i, Real.sq_sqrt (hv0 i)] at h
    nlinarith
  have hsin (i : Fin 3) : Real.sin (b i) ≤ Real.sin (a i) := by
    apply Real.sin_le_sin_of_le_of_le_pi_div_two
    · linarith [hb0 i, Real.pi_pos]
    · exact ha2 i
    · exact hb_le i
  have hsa (i : Fin 3) : 0 ≤ Real.sin (a i) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (ha0 i) (by linarith [ha2 i, Real.pi_pos])
  have hsb (i : Fin 3) : 0 ≤ Real.sin (b i) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (hb0 i)
      (by linarith [hb_le i, ha2 i, Real.pi_pos])
  have hsquare (i : Fin 3) : Real.sin (b i) ^ 2 ≤ 1 - v i := by
    have hmul := mul_nonneg (sub_nonneg.mpr (hsin i)) (add_nonneg (hsa i) (hsb i))
    have h := hvia i
    nlinarith
  have hprod01 : Real.sin (b 0) * Real.sin (b 1) ≤ Real.sin (a 0) * Real.sin (a 1) :=
    mul_le_mul (hsin 0) (hsin 1) (hsb 1) (hsa 0)
  have hprod : Real.sin (b 0) * Real.sin (b 1) * Real.sin (b 2) ≤
      Real.sin (a 0) * Real.sin (a 1) * Real.sin (a 2) :=
    mul_le_mul hprod01 (hsin 2) (hsb 2) (mul_nonneg (hsa 0) (hsa 1))
  have hsqrt : Real.sqrt ((1 - v 0) * (1 - v 1) * (1 - v 2)) =
      Real.sin (a 0) * Real.sin (a 1) * Real.sin (a 2) := by
    rw [← hvia 0, ← hvia 1, ← hvia 2]
    rw [show Real.sin (a 0) ^ 2 * Real.sin (a 1) ^ 2 * Real.sin (a 2) ^ 2 =
      (Real.sin (a 0) * Real.sin (a 1) * Real.sin (a 2)) ^ 2 by ring]
    exact Real.sqrt_sq (mul_nonneg (mul_nonneg (hsa 0) (hsa 1)) (hsa 2))
  have hbnd := sin_sq_sum_boundary hb_sum
  rw [hsqrt]
  have h0 := hsquare 0
  have h1 := hsquare 1
  have h2 := hsquare 2
  linarith

theorem rectangular_region (φ : PolMul.Spectral ℂ) :
    theta φ 0 + theta φ 1 + theta φ 2 ≤
      2 + 2 * Real.sqrt ((1 - theta φ 0) * (1 - theta φ 1) * (1 - theta φ 2)) := by
  apply angular_rectangular (fun i => theta φ i)
  · exact fun i => (theta_mem_Icc φ i).1
  · exact fun i => (theta_mem_Icc φ i).2
  · exact PolMulRect.angular_of_quadratic_bound (theta φ)
      (fun i => (theta_mem_Icc φ i).1) (fun i => (theta_mem_Icc φ i).2)
      (PolMulRect.quadratic_bound φ)

theorem proof_R88_8 : S_R88_8 := rectangular_region

end OM.NNN22
