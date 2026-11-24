import Lib.OM.Formats.Rates

/-! # Rectangular matrix multiplication as a witness for format exponents -/

noncomputable section
namespace OM.Formats

open Semicontinuity OmegaBound Foundations.PairUnitExponents Foundations.OrientationTransport

/-- At any integral base, a rectangular matrix tensor whose bonds cover the three
aspects has asymptotic rank at least that base to the rectangular exponent. -/
theorem rpow_rect_le_rank {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    {n A B C : ℕ+} (hn : 2 ≤ n)
    (hA : (n : ℝ)^x ≤ A) (hB : (n : ℝ)^y ≤ B) (hC : (n : ℝ)^z ≤ C) :
    (n : ℝ)^omegaRect3 ℂ x y z ≤ asympRank (PolMul.matMul (F := ℂ) B C A) := by
  obtain ⟨φ, hφ⟩ := (PolMulRect.omegaRect_isGreatest ℂ hx hy hz).1
  change PolMulRect.mmWeight φ x y z = PolMul.omegaRect ℂ x y z at hφ
  -- Rotate the maximizing point to match the tensor with bonds in order B, C, A.
  let σ : Equiv.Perm (Fin 3) := (Equiv.swap 0 2).trans (Equiv.swap 0 1)
  let ψ := pullPoint φ σ
  have weight : PolMulRect.mmWeight φ x y z =
      y * theta ψ 1 + z * theta ψ 2 + x * theta ψ 0 := by
    simp only [PolMulRect.mmWeight, ψ, theta_legReindex]
    change x * theta φ 1 + y * theta φ 2 + z * theta φ 0 =
      y * theta φ 2 + z * theta φ 0 + x * theta φ 1
    ring
  have side {u : ℝ} {D : ℕ+} (h : (n : ℝ)^u ≤ D) (i : Fin 3) :
      ((n : ℝ)^u)^theta ψ i ≤ (D : ℝ)^theta ψ i :=
    Real.rpow_le_rpow (by positivity) h (theta_mem_Icc ψ i).1
  rw [PolMulRect.omegaRect3_eq_omegaRect, ← hφ, weight]
  refine le_trans ?_ (NNN34.spectral_le_concrete ψ (PolMul.matMul B C A))
  have hn₀ := zero_lt_one.trans (cast_one_lt n hn)
  simp only [Omega.eval_matMul, Real.rpow_add hn₀, Real.rpow_mul hn₀.le]
  exact mul_le_mul (mul_le_mul (side hB 1) (side hC 2) (by positivity) (by positivity))
    (side hA 0) (by positivity) (by positivity)

/-- Three rounded matrix bonds approach any positive aspect triple from below. -/
theorem rect_le_beta {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    omegaRect3 ℂ x y z ≤ formatBeta (y+z) (z+x) (x+y) := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := min (ε/3) (min x (min y z))
  have hδ : 0 < δ := lt_min (by positivity) (lt_min hx (lt_min hy hz))
  have dx : 0 ≤ x-δ := sub_nonneg.mpr ((min_le_right ..).trans (min_le_left ..))
  have dy : 0 ≤ y-δ := sub_nonneg.mpr ((min_le_right ..).trans ((min_le_right ..).trans (min_le_left ..)))
  have dz : 0 ≤ z-δ := sub_nonneg.mpr ((min_le_right ..).trans ((min_le_right ..).trans (min_le_right ..)))
  obtain ⟨m, hm⟩ := exists_nat_gt (max 2 ((2 : ℝ)^(1/δ)))
  have hm₂ : (2:ℝ) < m := (le_max_left ..).trans_lt hm
  let n : ℕ+ := ⟨m, by exact_mod_cast (show (0:ℝ) < m by linarith)⟩
  have hn : 2 ≤ n := by exact_mod_cast hm₂.le
  have large : (2:ℝ) ≤ (n:ℝ)^δ := by
    have pow := Real.rpow_le_rpow (by positivity) ((le_max_right ..).trans hm.le) hδ.le
    rwa [← Real.rpow_mul (by norm_num), one_div_mul_cancel hδ.ne', Real.rpow_one] at pow
  let A := dim n (x-δ)
  let B := dim n (y-δ)
  let C := dim n (z-δ)
  have fit {u : ℝ} (hu : 0 ≤ u-δ) : ((dim n (u-δ) : ℕ) : ℝ) ≤ (n:ℝ)^u := by
    refine (PolMulRect.ceil_rpow_le_two_mul n.pos hu).trans ?_
    calc
      2*(n:ℝ)^(u-δ) ≤ (n:ℝ)^δ*(n:ℝ)^(u-δ) := mul_le_mul_of_nonneg_right large (by positivity)
      _ = _ := by rw [← Real.rpow_add (by positivity : (0:ℝ) < n)]; congr 1; ring
  have bond {i j : ℕ+} {u v : ℝ} (hi : (i:ℝ) ≤ (n:ℝ)^u) (hj : (j:ℝ) ≤ (n:ℝ)^v) :
      (((i*j : ℕ+) : ℕ) : ℝ) ≤ (n:ℝ)^(u+v) := by
    rw [PNat.mul_coe,Nat.cast_mul,Real.rpow_add (by positivity : (0:ℝ)<n)]
    exact mul_le_mul hi hj (by positivity) (by positivity)
  have lower := rpow_rect_le_rank dx dy dz hn (A := A) (B := B) (C := C) (Nat.le_ceil _)
    (Nat.le_ceil _) (Nat.le_ceil _)
  let M := PolMul.matMul (F := ℂ) B C A
  have pos : 0 < asympRank M := (Real.rpow_pos_of_pos (by positivity) _).trans_le lower
  have hβ := log_rank_le_beta (y := ![y+z,z+x,x+y]) (by
      intro i; fin_cases i <;> simp <;> positivity) M hn (by
    intro i; fin_cases i
    · exact bond (fit dy) (fit dz)
    · exact bond (fit dz) (fit dx)
    · exact bond (fit dx) (fit dy)) pos
  have small := ((Real.le_logb_iff_rpow_le (cast_one_lt n hn) pos).mpr lower).trans hβ
  have near := NNN36.omegaRect3_le_add (F := ℂ) hδ.le dx dy dz
    (a' := x) (b' := y) (c' := z) (by linarith) (by linarith) (by linarith)
  change omegaRect3 ℂ (x-δ) (y-δ) (z-δ) ≤ formatBeta (y+z) (z+x) (x+y) at small
  linarith only [near, small, show δ ≤ ε/3 from min_le_left ..]

end OM.Formats
