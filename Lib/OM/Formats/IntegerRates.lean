import Lib.OM.Formats.Rates

/-! # The exponent along powers of a fixed integral format -/

noncomputable section
namespace OM.Formats

open Filter Topology Semicontinuity P2M.R115

def powerLog (m n p : ℕ+) (t : ℕ) := Real.logb 2 (formatRankSup (m^t) (n^t) (p^t))

private theorem repeat_power (m n p : ℕ+) {s k t : ℕ} (hfit : s*k ≤ t) :
    k * powerLog m n p s ≤ powerLog m n p t := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa [powerLog] using Real.logb_nonneg one_lt_two (one_le_sup (m^t) (n^t) (p^t))
  have hkR : 0 < (k:ℝ) := by exact_mod_cast hk
  rw [mul_comm,← le_div_iff₀ hkR]
  apply (Real.logb_le_iff_le_rpow one_lt_two (NNN36.formatRankSup_pos ..)).mpr
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨T,rfl⟩
  by_cases hp : 0 < asympRank T
  · apply (Real.logb_le_iff_le_rpow one_lt_two hp).mp
    apply (le_div_iff₀ hkR).mpr
    let S := PolMul.kronPow T k
    have widths (X : ℕ+) : (((X^s)^k:ℕ+):ℕ) ≤ (X^t:ℕ+):= by
      change ((X:ℕ)^s)^k ≤ (X:ℕ)^t
      rw [← pow_mul]; exact Nat.pow_le_pow_right X.pos hfit
    have rank := rank_le_format S (m^t) (n^t) (p^t) (fun i => by
      fin_cases i <;> first | exact widths m | exact widths n | exact widths p)
    have eqn : asympRank S = (asympRank T)^k := by
      rw [← NNN34.class_asympRank_eq,← NNN34.class_asympRank_eq T,PolMul.DegenAsymp.mk_kronPow,
        AsymptoticSpectrumDuality.StrassenPreorder.asympRank_pow]
    rw [eqn] at rank
    simpa only [Real.logb_pow,mul_comm (k:ℝ),powerLog] using Real.logb_le_logb_of_le one_lt_two (pow_pos hp k) rank
  · exact (not_lt.mp hp).trans (by positivity)

/-- Replicating a fixed tensor shows that the best normalized power exponent
is a limit, including along powers not divisible by its original scale. -/
private theorem power_limit (m n p : ℕ+) :
    ∃ B : ℝ, 0 ≤ B ∧ (∀ t : ℕ, powerLog m n p t / t ≤ B) ∧
      Tendsto (fun t : ℕ => powerLog m n p t / t) atTop (𝓝 B) := by
  let f (t : ℕ) := powerLog m n p t / t
  have nonneg (t : ℕ) : 0 ≤ f t := div_nonneg (Real.logb_nonneg one_lt_two (one_le_sup ..)) (Nat.cast_nonneg _)
  have bound : BddAbove (Set.range f) := by
    refine ⟨Real.logb 2 (m:ℕ)+Real.logb 2 (n:ℕ),?_⟩
    rintro _ ⟨t,rfl⟩
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp only [f,Nat.cast_zero,div_zero]
      exact add_nonneg (Real.logb_nonneg one_lt_two (by exact_mod_cast m.pos))
        (Real.logb_nonneg one_lt_two (by exact_mod_cast n.pos))
    · apply (div_le_iff₀ (show 0 < (t:ℝ) by exact_mod_cast ht)).mpr
      have H := Real.logb_le_logb_of_le one_lt_two (NNN36.formatRankSup_pos ..) (NNN36.format_bounds (m^t) (n^t) (p^t)).2
      rw [PNat.pow_coe,PNat.pow_coe,Nat.cast_mul,Nat.cast_pow,Nat.cast_pow,Real.logb_mul (by positivity) (by positivity),
        Real.logb_pow,Real.logb_pow] at H
      exact H.trans_eq (by ring)
  let B := sSup (Set.range f)
  have upper (t : ℕ) : f t ≤ B := le_csSup bound ⟨t,rfl⟩
  refine ⟨B,(nonneg 0).trans (upper 0),upper,tendsto_order.mpr ⟨?_,fun b hb => Eventually.of_forall fun t => (upper t).trans_lt hb⟩⟩
  intro b hb
  obtain ⟨_,⟨s,rfl⟩,hs⟩ := exists_lt_of_lt_csSup (Set.range_nonempty f) hb
  rcases Nat.eq_zero_or_pos s with rfl | hs0
  · change b < powerLog m n p 0 / (0:ℕ) at hs
    simp only [Nat.cast_zero,div_zero] at hs
    exact Eventually.of_forall fun t => hs.trans_le (nonneg t)
  have hsr : 0 < (s:ℝ) := by exact_mod_cast hs0
  let k (t : ℕ) := ⌊(s:ℝ)⁻¹*t⌋₊
  have lim : Tendsto (fun t : ℕ => ((k t:ℝ)/t)*powerLog m n p s) atTop (𝓝 (f s)) := by
    simpa only [f,k,Function.comp_apply,div_eq_inv_mul] using ((tendsto_nat_floor_mul_div_atTop (inv_nonneg.mpr hsr.le)).comp
      (tendsto_natCast_atTop_atTop (R:=ℝ))).mul_const (powerLog m n p s)
  filter_upwards [lim.eventually (Ioi_mem_nhds hs),eventually_ge_atTop 1] with t h ht
  refine lt_of_lt_of_le h ?_
  have fit : s*k t ≤ t := by
    have H := Nat.floor_le (mul_nonneg (inv_nonneg.mpr hsr.le) (show 0 ≤ (t:ℝ) by positivity))
    have H' := mul_le_mul_of_nonneg_left H hsr.le
    rw [← mul_assoc,mul_inv_cancel₀ hsr.ne',one_mul] at H'
    exact_mod_cast H'
  have htR : 0 < (t:ℝ) := by exact_mod_cast ht
  apply (le_div_iff₀ htR).mpr
  calc
    _ = (k t:ℝ)*powerLog m n p s := by field_simp
    _ ≤ _ := repeat_power m n p fit

/-- At logarithms of positive integer dimensions the paper's rounded-base
limsup is the ordinary limit along powers of the original three dimensions. -/
theorem integer_format_limit (m n p : ℕ+) :
    Tendsto (fun t : ℕ => Real.logb 2 (formatRankSup (m^t) (n^t) (p^t))/t) atTop
      (𝓝 (P2M.R116.formatBeta (Real.logb 2 (m:ℕ)) (Real.logb 2 (n:ℕ)) (Real.logb 2 (p:ℕ)))) := by
  let lg (X : ℕ+) := Real.logb 2 (X:ℕ)
  have lg0 (X : ℕ+) : 0 ≤ lg X := Real.logb_nonneg one_lt_two (by exact_mod_cast X.pos)
  have id2 (X : ℕ+) : (2:ℝ)^lg X = (X:ℕ) :=
    Real.rpow_logb (by norm_num) (by norm_num) (by positivity)
  obtain ⟨B,hB,cap,lim⟩ := power_limit m n p
  let f := baseRate (lg m) (lg n) (lg p)
  have grow := (Real.tendsto_logb_atTop one_lt_two).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ) |>.comp tendsto_PNat_val_atTop_atTop)
  have upper : formatBeta (lg m) (lg n) (lg p) ≤ B := by
    have cb : atTop.IsCoboundedUnder (· ≤ ·) f :=
      isCoboundedUnder_le_of_eventually_le _ ((eventually_ge_atTop (2:ℕ+)).mono fun j hj => rate_nonneg _ _ _ j hj)
    apply (limsup_le_iff' cb (rate_bounded (lg0 m) (lg0 n))).mpr
    intro U hU
    filter_upwards [eventually_ge_atTop (2:ℕ+),grow.eventually_ge_atTop (B/(U-B))] with j hj hlarge
    let L := lg j
    let t := ⌈L⌉₊
    have hL : 0 < L := Real.logb_pos one_lt_two (cast_one_lt j hj)
    have ht : 0 < t := Nat.ceil_pos.mpr hL
    have htR : 0 < (t:ℝ) := by exact_mod_cast ht
    have fit (X : ℕ+) : (dim j (lg X):ℕ) ≤ (X^t:ℕ+) := by
      apply Nat.ceil_le.mpr
      calc
        (((j:ℕ):ℝ)^lg X) = (2:ℝ)^(L*lg X) := by rw [Real.rpow_mul (by norm_num),id2]
        _ ≤ (2:ℝ)^((t:ℝ)*lg X) := Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (lg0 X))
        _ = ((X^t:ℕ+):ℕ) := by rw [mul_comm,Real.rpow_mul (by norm_num),id2,Real.rpow_natCast,PNat.pow_coe,Nat.cast_pow]
    have A : formatRankSup (dim j (lg m)) (dim j (lg n)) (dim j (lg p)) ≤ formatRankSup (m^t) (n^t) (p^t) := by
      apply csSup_le (Set.range_nonempty _)
      rintro _ ⟨T,rfl⟩
      exact rank_le_format T _ _ _ (fun i => by fin_cases i <;> first | exact fit m | exact fit n | exact fit p)
    have H := Real.logb_le_logb_of_le one_lt_two (NNN36.formatRankSup_pos ..) A
    have eqn : L * f j = Real.logb 2 (formatRankSup (dim j (lg m)) (dim j (lg n)) (dim j (lg p))) :=
      Real.mul_logb (by positivity) (cast_one_lt j hj).ne' (by linarith [cast_one_lt j hj])
    rw [← eqn] at H
    change L * f j ≤ powerLog m n p t at H
    change B/(U-B) ≤ L at hlarge
    have round := Nat.ceil_lt_add_one hL.le
    change (t:ℝ) < L+1 at round
    apply le_of_mul_le_mul_left (a := L) _ hL
    nlinarith only [H,(div_le_iff₀ htR).mp (cap t),mul_le_mul_of_nonneg_left round.le hB,(div_le_iff₀ (sub_pos.mpr hU)).mp hlarge]
  have lower : B ≤ formatBeta (lg m) (lg n) (lg p) := by
    apply le_limsup_of_le (rate_bounded (lg0 m) (lg0 n))
    intro b eventual
    obtain ⟨j,hj⟩ := eventually_atTop.mp eventual
    apply le_of_tendsto lim
    filter_upwards [eventually_ge_atTop (max 1 (j:ℕ))] with t ht
    have ht0 := (le_max_left 1 (j:ℕ)).trans ht
    let k : ℕ+ := 2^t
    have large : j ≤ k := by
      change (j:ℕ) ≤ 2^t
      exact ((le_max_right ..).trans ht).trans (Nat.lt_two_pow_self.le)
    have castK : ((k:ℕ):ℝ) = (2:ℝ)^t := by simp [k]
    have dims (X : ℕ+) : dim k (lg X) = X^t := by
      apply PNat.eq
      change ⌈((k:ℕ):ℝ)^lg X⌉₊ = (X^t:ℕ+)
      rw [castK,← Real.rpow_natCast,← Real.rpow_mul (by norm_num),mul_comm,Real.rpow_mul (by norm_num),id2,Real.rpow_natCast]
      simpa using Nat.ceil_natCast (R:=ℝ) ((X:ℕ)^t)
    have h := hj k large
    unfold baseRate at h
    rw [dims,dims,dims,castK] at h
    change powerLog m n p t / t ≤ b
    simpa [Real.logb,powerLog,Real.log_pow,div_div,mul_comm] using h
  rw [show P2M.R116.formatBeta (lg m) (lg n) (lg p) = B from upper.antisymm lower]
  exact lim

/-- The three-rate exponent specializes exactly to the previously registered
cube exponent R114.2. -/
theorem cube_exponent : P2M.R116.formatBeta 1 1 1 = P2M.R114.beta := by
  have uniform := (NNN34.proof_R114_23 P2M.R114.beta).mp le_rfl
  refine le_antisymm ?_ ((NNN34.proof_R114_23 _).mpr ?_)
  · let f := baseRate 1 1 1
    have cb : atTop.IsCoboundedUnder (· ≤ ·) f := isCoboundedUnder_le_of_eventually_le _
      ((eventually_ge_atTop (2:ℕ+)).mono fun n hn => rate_nonneg _ _ _ n hn)
    apply limsup_le_of_le cb
    filter_upwards [eventually_ge_atTop (2:ℕ+)] with n hn
    have dims : dim n 1 = n := by apply PNat.eq; simp [dim]
    change Real.logb (n:ℕ) (formatRankSup (dim n 1) (dim n 1) (dim n 1)) ≤ _
    rw [dims]
    apply (Real.logb_le_iff_le_rpow (cast_one_lt n hn) (NNN36.formatRankSup_pos ..)).mpr
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨T,rfl⟩
    have lift {d : Fin 3 → ℕ+} (he : d = fun _ => n) (S : KTensor ℂ d) :
        asympRank S ≤ ((n:ℕ):ℝ)^P2M.R114.beta := by subst d; exact uniform n S
    exact lift (d := PolMul.fmt n n n) (by funext i; fin_cases i <;> rfl) T
  · intro n T
    by_cases hn : 2 ≤ n
    · by_cases hT : 0 < asympRank T
      · exact (Real.logb_le_iff_le_rpow (cast_one_lt n hn) hT).mp
          (log_rank_le_beta (y := fun _ => 1) (fun _ => zero_le_one) T hn (fun _ => by simp) hT)
      · exact (not_lt.mp hT).trans (by positivity)
    · have h : (n:ℕ) = 1 := by have hp := n.pos; change ¬2 ≤ (n:ℕ) at hn; omega
      simpa only [h,Nat.cast_one,Real.one_rpow] using uniform n T

end OM.Formats
