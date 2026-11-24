import PLATFORM.Statements.«R116.1»
import PLATFORM.Statements.«R116.2»
import Lib.OM.NNN36.TriangleBound
import Lib.OM.NNN32.Growth
import Lib.OM.NNN34.CubeRanks

/-! # Rounding and scaling of positive integral formats -/

noncomputable section
namespace OM.Formats

open Filter Topology Semicontinuity P2M.R115

def dim (n : ℕ+) (x : ℝ) : ℕ+ :=
  ⟨⌈((n : ℕ) : ℝ) ^ x⌉₊, Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by exact_mod_cast n.2) x)⟩

def baseRate (a b c : ℝ) (n : ℕ+) : ℝ :=
  Real.logb (n : ℕ) (formatRankSup (dim n a) (dim n b) (dim n c))

def formatBeta (a b c : ℝ) : ℝ := limsup (baseRate a b c) atTop

def discRadius (a b c : ℝ) : ℝ :=
  let s := (a+b+c)/2
  if c^2 < a^2+b^2 then a*b*c/(4*Real.sqrt (s*(s-a)*(s-b)*(s-c))) else c/2

lemma cast_one_lt (n : ℕ+) (hn : 2 ≤ n) : (1 : ℝ) < (n : ℕ) := by
  exact_mod_cast (show 1 < (n : ℕ) from hn)

lemma one_le_sup (m n p : ℕ+) : 1 ≤ formatRankSup m n p :=
  (show (1 : ℝ) ≤ (min (p : ℕ) ((m : ℕ) * (n : ℕ)) : ℕ) by
    exact_mod_cast le_min p.pos (Nat.mul_pos m.pos n.pos)).trans (NNN36.format_bounds ..).1

lemma rate_nonneg (a b c : ℝ) (n : ℕ+) (hn : 2 ≤ n) : 0 ≤ baseRate a b c n :=
  Real.logb_nonneg (cast_one_lt n hn) (one_le_sup ..)

lemma log_dim_bounds {n : ℕ+} {a : ℝ} (ha : 0 ≤ a) :
    Real.logb 2 (n : ℕ) * a ≤ Real.logb 2 (dim n a : ℕ) ∧
    Real.logb 2 (dim n a : ℕ) ≤ Real.logb 2 (n : ℕ) * a + 1 := by
  have hn : 0 < ((n : ℕ) : ℝ) := by positivity
  have hp := Real.rpow_pos_of_pos hn a
  have lo := Real.logb_le_logb_of_le one_lt_two hp (Nat.le_ceil (((n : ℕ) : ℝ)^a))
  have hi := Real.logb_le_logb_of_le one_lt_two (show 0 < ((dim n a : ℕ) : ℝ) by positivity)
    (PolMulRect.ceil_rpow_le_two_mul n.pos ha)
  rw [Real.logb_mul (by norm_num) hp.ne', Real.logb_self_eq_one one_lt_two] at hi
  rw [Real.logb_rpow_eq_mul_logb_of_pos hn] at lo hi
  exact ⟨(mul_comm ..).trans_le lo, hi.trans_eq (by ring)⟩

lemma rate_bounded {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    atTop.IsBoundedUnder (· ≤ ·) (baseRate a b c) := by
  refine isBoundedUnder_of_eventually_le (a := a+b+2) ?_
  filter_upwards [eventually_ge_atTop (2 : ℕ+)] with n hn
  have hn' := cast_one_lt n hn
  have fit (x : ℝ) (hx : 0 ≤ x) : ((dim n x : ℕ) : ℝ) ≤ (n : ℝ)^(x+1) := by
    rw [Real.rpow_add_one (by positivity : (n : ℝ) ≠ 0)]
    exact (PolMulRect.ceil_rpow_le_two_mul n.pos hx).trans
      ((mul_le_mul_of_nonneg_right (by exact_mod_cast hn : (2 : ℝ) ≤ n) (by positivity)).trans_eq (mul_comm ..))
  apply (Real.logb_le_iff_le_rpow hn' (NNN36.formatRankSup_pos ..)).mpr
  refine (NNN36.format_bounds ..).2.trans ?_
  rw [Nat.cast_mul, show a+b+2 = (a+1)+(b+1) by ring, Real.rpow_add (by positivity)]
  exact mul_le_mul (fit a ha) (fit b hb) (by positivity) (by positivity)

lemma rank_le_format {d : Fin 3 → ℕ+} (T : KTensor ℂ d) (m n p : ℕ+)
    (h : ∀ i, (d i : ℕ) ≤ (PolMul.fmt m n p i : ℕ)) :
    asympRank T ≤ formatRankSup m n p := by
  obtain ⟨S,hS⟩ := exists_reembed_of_le h T
  rw [← hS]
  exact le_csSup ⟨_, by rintro _ ⟨W,rfl⟩; exact NNN36.asympRank_le_first_two W⟩ ⟨S,rfl⟩

/-- A power that fits the unrounded dimensions can be tested at arbitrarily large bases. -/
theorem log_rank_le_beta {y : Fin 3 → ℝ} (hy : ∀ i, 0 ≤ y i)
    {d : Fin 3 → ℕ+} (T : KTensor ℂ d) {m : ℕ+} (hm : 2 ≤ m)
    (hfit : ∀ i, ((d i : ℕ) : ℝ) ≤ ((m : ℕ) : ℝ)^(y i)) (hT : 0 < asympRank T) :
    Real.logb (m : ℕ) (asympRank T) ≤ formatBeta (y 0) (y 1) (y 2) := by
  apply le_limsup_of_le (rate_bounded (hy 0) (hy 1))
  intro B hB
  obtain ⟨N,hN⟩ := eventually_atTop.mp hB
  let k : ℕ := N
  have hk : 0 < k := N.pos
  have large : N ≤ m^k := by
    change (N : ℕ) ≤ (m : ℕ)^k
    exact (Nat.lt_two_pow_self (n := (N : ℕ))).le.trans (Nat.pow_le_pow_left hm k)
  have hm' := cast_one_lt m hm
  have hmk : (1 : ℝ) < ((m^k : ℕ+) : ℕ) := by
    simpa using one_lt_pow₀ hm' hk.ne'
  let S := PolMul.kronPow T k
  have hdim (i : Fin 3) : ((d i ^ k : ℕ+) : ℕ) ≤ (dim (m ^ k) (y i) : ℕ) := by
    apply Nat.cast_le (α := ℝ) |>.mp
    apply le_trans _ (Nat.le_ceil _)
    simpa only [PNat.pow_coe, Nat.cast_pow, Real.rpow_pow_comm (by positivity : (0:ℝ) ≤ (m:ℕ))]
      using pow_le_pow_left₀ (Nat.cast_nonneg _) (hfit i) k
  have hsup := rank_le_format S (dim (m^k) (y 0)) (dim (m^k) (y 1)) (dim (m^k) (y 2))
    (fun i => by fin_cases i <;> exact hdim _)
  have hrank : asympRank S = (asympRank T)^k := by
    rw [← NNN34.class_asympRank_eq, ← NNN34.class_asympRank_eq T, PolMul.DegenAsymp.mk_kronPow,
      AsymptoticSpectrumDuality.StrassenPreorder.asympRank_pow]
  rw [hrank] at hsup
  have hh := (Real.logb_le_logb_of_le hmk (pow_pos hT k) hsup).trans (hN (m^k) large)
  simpa [Real.logb, Real.log_pow, k, ne_of_gt (by exact_mod_cast hk : (0 : ℝ) < (N : ℕ)),
    mul_div_mul_left] using hh

lemma flattening_rate {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : c ≤ a+b) :
    c ≤ formatBeta a b c := by
  apply le_limsup_of_le (rate_bounded ha hb)
  intro B hB
  obtain ⟨n, hn, h⟩ := (eventually_ge_atTop (2 : ℕ+) |>.and hB).exists
  apply le_trans _ h
  apply (Real.le_logb_iff_rpow_le (cast_one_lt n hn) (NNN36.formatRankSup_pos ..)).mpr
  refine le_trans ?_ (NNN36.format_bounds ..).1
  rw [Nat.cast_min, Nat.cast_mul]
  apply le_min (Nat.le_ceil _)
  apply (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast n.pos) hc).trans
  rw [Real.rpow_add (by positivity)]
  exact mul_le_mul (Nat.le_ceil _) (Nat.le_ceil _) (by positivity) (by positivity)

end OM.Formats
