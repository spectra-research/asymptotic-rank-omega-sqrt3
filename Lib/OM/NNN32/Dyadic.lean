import Lib.OM.NNN32.PowerRestriction
import PLATFORM.Statements.«R113.8»

/-! # The finite saving and the uniform dyadic rank bounds -/

noncomputable section

namespace OM.NNN32

open Semicontinuity Filter Topology

/-- Logarithm of the summand weight, including both cut ranks. -/
lemma twice_log_weight {d : Fin 4 → ℕ+} {T : KTensor ℂ d} (hn : T ≠ 0) :
    2 * Real.logb 2 (weight T) =
      Real.logb 2 (flatRank T {0,1}) + Real.logb 2 (flatRank T {0,2}) := by
  have ha : (0 : ℝ) < flatRank T {0,1} := by exact_mod_cast flatRank_pos hn {0,1}
  have hb : (0 : ℝ) < flatRank T {0,2} := by exact_mod_cast flatRank_pos hn {0,2}
  change (↑(2 : ℕ) : ℝ) * _ = _
  rw [← Real.logb_pow, weight, Real.sq_sqrt (mul_nonneg ha.le hb.le), Real.logb_mul ha.ne' hb.ne']

private lemma count_limit (m : ℕ) (n : ℕ → ℕ) (hn : ∀ L, n L ≤ L) :
    Tendsto (fun L : ℕ => Real.logb 2 (((n L+2)^m : ℕ) : ℝ) / L) atTop (𝓝 0) := by
  have ht : Tendsto (fun L : ℕ => (L : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hh := (Real.tendsto_pow_logb_div_mul_add_atTop (b := 2) 1 (-2) 1 one_ne_zero).comp ht
  have hh' : Tendsto (fun L : ℕ => Real.logb 2 ((L : ℝ)+2) / L) atTop (𝓝 0) := by
    simpa [Function.comp_def, add_assoc] using hh
  apply squeeze_zero (fun L => div_nonneg (Real.logb_nonneg (by norm_num)
    (by exact_mod_cast Nat.one_le_pow m (n L+2) (by omega))) (Nat.cast_nonneg L)) _
    (by simpa [mul_div_assoc] using hh'.const_mul (m : ℝ))
  intro L
  rw [Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat, Real.logb_pow]
  rw [← mul_div_assoc]
  gcongr <;> first | exact hn L | norm_num

private theorem dyadic_of_finite :
    finiteWitness → (∃ κ : ℝ, κ < 2 * Real.sqrt 2 ∧
      ∃ (m : ℕ → ℕ) (B : (L : ℕ) → Fin (m L) → KTensor ℂ (fun _ : Fin 4 => (2 : ℕ+) ^ L)),
        (∀ L, (∑ j, B L j) = crossing ((2 : ℕ+) ^ L)) ∧
        Tendsto (fun L : ℕ => Real.logb 2 (m L) / L) atTop (𝓝 0) ∧
        ∀ ε : ℝ, 0 < ε → ∀ᶠ L : ℕ in atTop, ∀ j : Fin (m L), B L j ≠ 0 →
          Real.logb 2 (flatRank (B L j) {0,1}) + Real.logb 2 (flatRank (B L j) {0,2}) ≤
            (κ+ε)*L) := by
  rintro ⟨D,hD,c,hcost,hstrict⟩
  have hc := one_le_cost hcost
  obtain ⟨m,B,hB,hcB⟩ := hcost
  change c = ∑ j, weight (B j) at hcB
  have hD2 : (2 : ℝ) ≤ (D : ℕ) := by exact_mod_cast hD
  have hD0 : (0 : ℝ) < (D : ℕ) := by linarith
  let b := Real.logb 2 (D : ℕ)
  let a := Real.logb 2 c
  have hb : 1 ≤ b := by
    simpa [b, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using
      Real.logb_le_logb_of_le (b := 2) (by norm_num) (by norm_num : (0:ℝ)<2) hD2
  have hb0 : 0 < b := by linarith
  have ha : 0 ≤ a := Real.logb_nonneg (by norm_num) hc
  have hab : a < Real.sqrt 2 * b := by
    simpa [a,b,Real.logb_rpow_eq_mul_logb_of_pos hD0] using
      Real.logb_lt_logb (b := 2) (by norm_num) (lt_of_lt_of_le zero_lt_one hc) hstrict
  let n (L : ℕ) := ⌊(L : ℝ) / b⌋₊
  have hn (L : ℕ) : (n L : ℝ) ≤ L / b := Nat.floor_le (by positivity)
  have hpow (L : ℕ) : ((2 : ℕ+) ^ L : ℕ) ≤ (D : ℕ) ^ (n L+1) := by
    have hfloor := Nat.lt_floor_add_one ((L : ℝ) / b)
    have hle : (L : ℝ) ≤ ((n L : ℝ)+1)*b := ((div_lt_iff₀ hb0).1 hfloor).le
    have hlog : Real.logb 2 ((2 : ℝ)^L) ≤ Real.logb 2 (((D : ℕ) : ℝ)^(n L+1)) := by
      simpa [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), b] using hle
    have := (Real.logb_le_logb (by norm_num) (by positivity) (by positivity)).1 hlog
    exact_mod_cast this
  choose A hs hw using fun L => grouped_crossing (E := (2 : ℕ+)^L) B hB (n L) (hpow L)
  refine ⟨2 * a / b, (div_lt_iff₀ hb0).2 (by linarith), _, A, hs, count_limit m n ?_, ?_⟩
  · intro L
    exact_mod_cast (hn L).trans ((div_le_self (Nat.cast_nonneg L) hb))
  · intro ε hε
    obtain ⟨L₀,hL₀⟩ := exists_nat_ge (2*a/ε)
    filter_upwards [eventually_ge_atTop L₀] with L hL
    intro j hj
    have hw' := hw L j
    rw [← hcB] at hw'
    have hlog := Real.logb_le_logb_of_le (b := 2) (by norm_num)
      (zero_lt_one.trans_le (one_le_weight hj)) hw'
    rw [Real.logb_pow, Nat.cast_add, Nat.cast_one] at hlog
    have hsmall : 2*a ≤ (L : ℝ)*ε := (div_le_iff₀ hε).1
      (hL₀.trans (by exact_mod_cast hL))
    rw [← twice_log_weight hj]
    have hmul := mul_le_mul_of_nonneg_right (hn L) ha
    change Real.logb 2 (weight _) ≤ ((n L : ℝ)+1)*a at hlog
    calc
      _ ≤ 2*(L/b*a) + 2*a := by linarith
      _ ≤ (2*a/b + ε)*L := by linarith only [hsmall, show 2*((L:ℝ)/b*a) = (2*a/b)*L by ring]

/-- An upper bound on the dyadic log-ranks with a strict margin produces a finite
expansion below any specified exponent. -/
theorem saving_of_dyadic {t κ : ℝ} (hκ : κ < 2*t)
    (m : ℕ → ℕ) (B : (L : ℕ) → Fin (m L) → KTensor ℂ (fun _ : Fin 4 => (2 : ℕ+)^L))
    (hs : ∀ L, (∑ j, B L j) = crossing ((2 : ℕ+)^L))
    (hm : Tendsto (fun L : ℕ => Real.logb 2 (m L) / L) atTop (𝓝 0))
    (hr : ∀ ε : ℝ, 0 < ε → ∀ᶠ L : ℕ in atTop, ∀ j : Fin (m L), B L j ≠ 0 →
      Real.logb 2 (flatRank (B L j) {0,1}) + Real.logb 2 (flatRank (B L j) {0,2}) ≤ (κ+ε)*L) :
    ∃ D : ℕ+, 2 ≤ D ∧ ∃ c ∈ expansionCosts (crossing D), c < ((D : ℕ) : ℝ)^t := by
  let ε := (2 * t - κ) / 4
  have he : 0 < ε := by dsimp [ε]; linarith
  have hcount := (tendsto_order.1 hm).2 ε he
  obtain ⟨L,hL,hmL,hrL⟩ := ((eventually_ge_atTop 1).and (hcount.and (hr ε he))).exists
  have hp : 0 < L := hL
  have hLR : (0 : ℝ) < L := by exact_mod_cast hp
  have hmp : 0 < m L := by
    by_contra! hn
    have : IsEmpty (Fin (m L)) := by rw [Nat.eq_zero_of_le_zero hn]; infer_instance
    apply crossing_ne_zero ((2 : ℕ+) ^ L)
    calc
      _ = ∑ j, B L j := (hs L).symm
      _ = 0 := Finset.sum_of_isEmpty _
  have hmR : (0 : ℝ) < m L := by exact_mod_cast hmp
  have hmle := (Real.logb_lt_iff_lt_rpow (b := 2) (by norm_num) hmR).1
    ((div_lt_iff₀ hLR).1 hmL)
  have hterm (j : Fin (m L)) : weight (B L j) ≤ (2 : ℝ)^((κ+ε)*L/2) := by
    by_cases hj : B L j = 0
    · rw [hj, weight_zero]; positivity
    · apply (Real.logb_le_iff_le_rpow (by norm_num) (zero_lt_one.trans_le (one_le_weight hj))).1
      have := hrL j hj
      rw [← twice_log_weight hj] at this
      linarith
  refine ⟨(2 : ℕ+)^L, ?_, ∑ j, weight (B L j), ⟨m L, B L, hs L, rfl⟩, ?_⟩
  · simpa using (pow_le_pow_right' (by norm_num : (1 : ℕ+) ≤ 2) hL)
  calc
    _ ≤ ∑ _j : Fin (m L), (2 : ℝ)^((κ+ε)*L/2) := Finset.sum_le_sum fun j _ => hterm j
    _ = (m L : ℝ) * 2^((κ+ε)*L/2) := by simp
    _ < 2^(ε*L) * 2^((κ+ε)*L/2) := mul_lt_mul_of_pos_right hmle (by positivity)
    _ = (2 : ℝ)^(ε*L+(κ+ε)*L/2) := (Real.rpow_add (by norm_num) _ _).symm
    _ < (2 : ℝ)^((L : ℝ)*t) := by
      apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
      have hh : ε + (κ+ε)/2 < t := by dsimp [ε]; linarith
      linarith only [mul_lt_mul_of_pos_right hh hLR]
    _ = _ := by rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]; norm_cast

theorem proof_R113_8 : S_R113_8 := by
  refine ⟨dyadic_of_finite, ?_⟩
  rintro ⟨κ,hκ,m,B,hs,hm,hr⟩
  exact saving_of_dyadic hκ m B hs hm hr

end OM.NNN32
