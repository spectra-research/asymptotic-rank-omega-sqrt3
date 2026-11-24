import Lib.OM.Formats.Rates
import Lib.OM.NNN24.FCont

/-! # Uniform spectral estimates pass to the three-rate limsup -/

noncomputable section
namespace OM.Formats

open Filter Topology Semicontinuity P2M.R115 NNN22

theorem beta_le_of_price {y : Fin 3 → ℝ} (hy : ∀ i, 0 < y i) {B : ℝ}
    (hB : ∀ φ : PolMul.Spectral ℂ, Fv φ y ≤ B) :
    formatBeta (y 0) (y 1) (y 2) ≤ B := by
  let f := baseRate (y 0) (y 1) (y 2)
  have hlow : atTop.IsCoboundedUnder (· ≤ ·) f :=
    isCoboundedUnder_le_of_eventually_le _ ((eventually_ge_atTop (2 : ℕ+)).mono fun n h => rate_nonneg _ _ _ n h)
  apply (limsup_le_iff' hlow (rate_bounded (hy 0).le (hy 1).le)).mpr
  intro U hU
  have grow := (Real.tendsto_logb_atTop one_lt_two).comp
    (tendsto_natCast_atTop_atTop (R := ℝ) |>.comp tendsto_PNat_val_atTop_atTop)
  filter_upwards [eventually_ge_atTop (2 : ℕ+), grow.eventually_ge_atTop (3/(U-B))] with n hn hlarge
  let L := Real.logb 2 (n : ℕ)
  have hL : 0 < L := Real.logb_pos one_lt_two (cast_one_lt n hn)
  change 3/(U-B) ≤ L at hlarge
  let d := PolMul.fmt (dim n (y 0)) (dim n (y 1)) (dim n (y 2))
  have hd (i : Fin 3) : d i = dim n (y i) := by fin_cases i <;> rfl
  have pos (i : Fin 3) : 0 < Real.logb 2 (d i : ℕ) := by
    rw [hd]; exact (mul_pos hL (hy i)).trans_le (log_dim_bounds (hy i).le).1
  have rankBound : formatRankSup (d 0) (d 1) (d 2) ≤ (2 : ℝ)^(L*B+3) := by
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨T,rfl⟩
    apply NNN.asympRank_le_of_spectral_bound T _ (by positivity)
    intro φ
    by_cases hv : 0 < φ.eval T
    · apply (Real.logb_le_iff_le_rpow one_lt_two hv).mp
      have he := NNN36.log_eval_le_Fv (d := d) φ T hv pos
      have nonneg (i : Fin 3) := mul_nonneg hL.le (hy i).le
      have hpad : Fv φ (fun i => L*y i + 1) ≤ Fv φ (fun i => L*y i) + 3 := by
        have h := NNN24.Mm.Fv_le_add_abs φ (y := fun i => L*y i + 1)
          (z := fun i => L*y i) (fun i => by linarith [nonneg i]) nonneg
        norm_num [NNN24.Mm.Fv_eq] at h ⊢
        exact h
      rw [Fv_smul φ (fun i => (hy i).le) hL.le] at hpad
      refine he.trans ((Fv_mono φ (y' := fun i => L*y i+1)
        (fun i => by rw [hd]; exact (log_dim_bounds (hy i).le).2)).trans ?_)
      exact hpad.trans (by linarith only [mul_le_mul_of_nonneg_left (hB φ) hL.le])
    · exact (not_lt.mp hv).trans (by positivity)
  apply (Real.logb_le_iff_le_rpow (cast_one_lt n hn) (NNN36.formatRankSup_pos ..)).mpr
  have toBase : ((n : ℕ) : ℝ)^U = (2 : ℝ)^(L*U) := by
    rw [Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) (by positivity)]
  rw [toBase]
  exact rankBound.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num)
    (by linarith only [(div_le_iff₀ (sub_pos.mpr hU)).mp hlarge]))

end OM.Formats
