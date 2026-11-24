import Lib.OM.NNN34.Crossing
import Lib.OM.NNN30.Partition.Main
import PLATFORM.Statements.«R114.13»

/-! # The cutoff and the complementary partition exponent -/

namespace OM.NNN34

open Filter Topology P2M.R114 OM.NNN30.Rect

private theorem cutoff_next (H : ℕ) (hH : 0 < H) :
    (partitionSide H : ℕ) < Qn (cutoff H + 1) := by
  have hk : cutoff H < H := by
    refine lt_of_le_of_ne (cutoff_le H) ?_
    intro he
    have h := cutoff_fits H
    rw [he, Qn, Finset.sum_range_succ] at h
    have hpos : 0 < ∑ j ∈ Finset.range H, Fintype.card j.Partition :=
      Finset.sum_pos (fun _ _ => Fintype.card_pos) ⟨0, Finset.mem_range.mpr hH⟩
    change _ ≤ Fintype.card H.Partition at h
    omega
  by_contra! h
  have he : cutoff H + 1 ≤ cutoff H := Nat.le_findGreatest hk h
  omega

theorem proof_R114_13 : S_R114_13 := by
  obtain ⟨C, hC, hp, hq⟩ := NNN30.Partition.proof_R108_2
  let P := fun H => (partitionSide H : ℕ)
  let lp := fun H => Real.logb 2 (P H)
  let lq := fun H => Real.logb 2 (Qn H)
  let root := fun H : ℕ => Real.sqrt (H : ℝ)
  change Tendsto (fun H => lp H / root H) atTop (𝓝 C) at hp
  replace hq : Tendsto (fun H => lq H / root H) atTop (𝓝 C) := by
    simpa only [lq, Qn, root, Nat.cast_sum] using hq
  have hpos : ∀ᶠ H : ℕ in atTop, 0 < (H : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with H hH
    exact_mod_cast hH
  have hlp : Tendsto lp atTop atTop := by
    have hr : Tendsto root atTop atTop := Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    apply (hp.pos_mul_atTop hC hr).congr'
    filter_upwards [hpos] with H hH
    exact div_mul_cancel₀ _ (Real.sqrt_pos.mpr hH).ne'
  have hP : Tendsto P atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [hlp.eventually_ge_atTop (Real.logb 2 ((b+1 : ℕ) : ℝ))] with H hh
    have hpr : 0 < (P H : ℝ) := by exact_mod_cast (partitionSide H).pos
    have h := (Real.logb_le_logb one_lt_two (by positivity) hpr).mp hh
    exact (Nat.le_succ b).trans (by exact_mod_cast h)
  have hk : Tendsto cutoff atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [hP.eventually_ge_atTop (Qn b), eventually_ge_atTop b] with H hQ hH
    exact Nat.le_findGreatest (P := fun j => Qn j ≤ P H) hH hQ
  let next := fun H => cutoff H + 1
  have hn : Tendsto next atTop atTop := (tendsto_add_atTop_nat 1).comp hk
  have hr : Tendsto (fun H => (lp H / root H) / (lq (next H) / root (next H))) atTop (𝓝 1) := by
    simpa only [div_self hC.ne', Function.comp_def, Pi.div_def] using! hp.div (hq.comp hn) hC.ne'
  have hinv : Tendsto (fun H : ℕ => 1 / (H : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using! tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hkRatio : Tendsto (fun H : ℕ => (cutoff H : ℝ) / H) atTop (𝓝 1) := by
    have lower := (hr.pow 2).sub hinv
    simp only [one_pow, sub_zero] at lower
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' lower tendsto_const_nhds
    · filter_upwards [hpos, (hq.comp hn).eventually (Ioi_mem_nhds hC)] with H hH hnext
      change 0 < lq (next H) / root (next H) at hnext
      have hroot := Real.sqrt_pos.mpr hH
      have hnpos : 0 < ((next H : ℕ) : ℝ) := by dsimp [next]; positivity
      have hnroot := Real.sqrt_pos.mpr hnpos
      have hlq : 0 < lq (next H) := (div_pos_iff_of_pos_right hnroot).mp hnext
      have hlog : lp H ≤ lq (next H) :=
        (Real.logb_le_logb one_lt_two (by exact_mod_cast (partitionSide H).pos)
          (by exact_mod_cast one_le_Qn _)).mpr
          (by exact_mod_cast (cutoff_next H (by exact_mod_cast hH)).le)
      have hLP0 : 0 ≤ lp H := Real.logb_nonneg one_lt_two (by exact_mod_cast (partitionSide H).pos)
      have hle : (lp H / root H) / (lq (next H) / root (next H)) ≤ root (next H) / root H := by
        apply (div_le_iff₀ hnext).mpr
        dsimp only [root]
        field_simp [hroot.ne', hnroot.ne']
        exact hlog
      have hsq := pow_le_pow_left₀ (div_nonneg (div_nonneg hLP0 hroot.le) hnext.le) hle 2
      have he : (root (next H) / root H)^2 = (cutoff H : ℝ)/H + 1/H := by
        dsimp only [root]
        rw [div_pow, Real.sq_sqrt hnpos.le, Real.sq_sqrt hH.le]
        simp only [next, Nat.cast_add, Nat.cast_one, add_div]
      exact sub_le_iff_le_add.mpr (hsq.trans_eq he)
    · filter_upwards [hpos] with H hH
      exact (div_le_one hH).mpr (by exact_mod_cast cutoff_le H)
  refine ⟨hP, hkRatio, ?_⟩
  let J := fun H => 4*H-cutoff H-1
  have hJ : Tendsto J atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (b+1)] with H hH
    dsimp only [J]; have := cutoff_le H; omega
  have hJR : Tendsto (fun H : ℕ => (J H : ℝ) / H) atTop (𝓝 3) := by
    have hfour : Tendsto (fun _ : ℕ => (4 : ℝ)) atTop (𝓝 4) := tendsto_const_nhds
    have hlim := (hfour.sub hkRatio).sub hinv
    norm_num at hlim
    apply hlim.congr'
    filter_upwards [hpos] with H hH
    have h1 : 1 ≤ H := by exact_mod_cast hH
    have hk' := cutoff_le H
    dsimp only [J]
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    field_simp
  have hlim := ((hq.comp hJ).div hp hC.ne').mul hJR.sqrt
  rw [div_self hC.ne', one_mul] at hlim
  apply hlim.congr'
  filter_upwards [hpos, hJ.eventually_ge_atTop 1] with H hH hj
  have hjpos : (0 : ℝ) < J H := by exact_mod_cast hj
  have hlog₂ : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  change (lq (J H) / root (J H) / (lp H / root H)) * Real.sqrt ((J H : ℝ) / H) = _
  rw [Real.sqrt_div hjpos.le]
  dsimp only [lp, lq, root, Real.logb, P, J]
  rw [show (4 * H - cutoff H - 1) = J H from rfl]
  field_simp [hlog₂, (Real.sqrt_pos.mpr hH).ne', (Real.sqrt_pos.mpr hjpos).ne'] <;> ring

end OM.NNN34

