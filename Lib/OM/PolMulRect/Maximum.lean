import Lib.OM.Omega
import Lib.OM.PolMulRect.Rank

/-! # Strassen's maximum for the rectangular exponent

Amanov, van den Berg and Zuiddam, Lemma 4.4. A fixed rounded block and its
tensor powers give ordinary-rank bounds at every input size.
-/

namespace OM.PolMulRect

open Semicontinuity AsymptoticSpectrumDuality Foundations.PairUnitExponents
open PolMul (matMul omegaRect Spectral)
open PolMul.OmegaBridge (strassenRank_mk_eq_tensorRank)

universe u
variable {F : Type u} [Field F]

/-- Each pair exponent is a logarithm of a positive continuous evaluation. -/
theorem continuous_mmWeight (F : Type u) [Field F] (a b c : ℝ) :
    Continuous (fun φ : AsymptoticSpectrum (tensorStrassenPreorder (F := F) (k := 3)
      (by norm_num)) => mmWeight φ a b c) := by
  let p := tensorStrassenPreorder (F := F) (k := 3) (by norm_num)
  have hθ (i : Fin 3) : Continuous (fun φ : AsymptoticSpectrum p => theta φ i) :=
    (AsymptoticSpectrum.continuous_eval p (orientedPairUnit F i 2)).logb
      (fun φ => (zero_lt_one.trans_le (one_le_eval_orientedPairUnit φ i 2 (by decide +kernel))).ne')
  exact ((continuous_const.mul (hθ 1)).add (continuous_const.mul (hθ 2))).add
    (continuous_const.mul (hθ 0))

private lemma exists_max_mmWeight (F : Type u) [Field F] (a b c : ℝ) :
    ∃ φ : Spectral F, ∀ ψ : Spectral F, mmWeight ψ a b c ≤ mmWeight φ a b c := by
  let p := tensorStrassenPreorder (F := F) (k := 3) (by norm_num)
  let _ : Nonempty (AsymptoticSpectrum p) := AsymptoticSpectrum.nonempty p
  obtain ⟨φ, _, hφ⟩ := (AsymptoticSpectrum.isCompact p).exists_isMaxOn
    Set.univ_nonempty (continuous_mmWeight F a b c).continuousOn
  exact ⟨φ, fun ψ => hφ (Set.mem_univ ψ)⟩

private lemma rpow_mmWeight (φ : Spectral F) {d : ℝ} (hd : 0 < d) (a b c : ℝ) :
    d ^ mmWeight φ a b c =
      (d ^ a) ^ theta φ 1 * (d ^ b) ^ theta φ 2 * (d ^ c) ^ theta φ 0 := by
  simp only [mmWeight, Real.rpow_add hd, Real.rpow_mul hd.le]

/-- Evaluating the rounded tensors gives a lower bound on every admissible exponent. -/
theorem mmWeight_le_omegaRect (φ : Spectral F) {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    mmWeight φ a b c ≤ omegaRect F a b c := by
  apply le_csInf (rectAdmissible_nonempty F ha hb hc)
  rintro τ ⟨K, hK⟩
  apply exponent_le_of_bound (K := K)
  intro n hn
  let T := matMul (F := F) (ceilSide n hn a) (ceilSide n hn b) (ceilSide n hn c)
  have heval : PolMul.Spectral.eval φ T ≤ (tensorRank T : ℝ) := by
    rw [← strassenRank_mk_eq_tensorRank]
    exact AsymptoticSpectrum.eval_le_rank _ φ _
  apply le_trans _ (heval.trans (hK n hn))
  dsimp only [T]
  rw [Omega.eval_matMul, rpow_mmWeight φ (by exact_mod_cast hn : 0 < (n : ℝ))]
  have side (x : ℝ) (i : Fin 3) : ((n : ℝ) ^ x) ^ theta φ i ≤
      ((ceilSide n hn x : ℕ) : ℝ) ^ theta φ i :=
    Real.rpow_le_rpow (by positivity) (Nat.le_ceil _) (theta_mem_Icc φ i).1
  exact mul_le_mul (mul_le_mul (side a 1) (side b 2) (by positivity) (by positivity))
    (side c 0) (by positivity) (by positivity)

private lemma one_le_matMul_class (A B C : ℕ+) :
    (PolMul.OmegaBridge.pF F).rel 1 (TensorClass.mk ⟨_, matMul (F := F) A B C⟩) := by
  rw [TensorClass.one_def]
  apply unitTensor_one_restricts_of_ne_zero
  intro hz
  have hr := mul_le_tensorRank_matMul (F := F) A B C
  rw [← strassenRank_mk_eq_tensorRank, hz] at hr
  exact (Nat.mul_pos A.pos B.pos).not_ge (hr.trans_eq ((PolMul.OmegaBridge.pF F).rank_natCast 0))

/-- A block chosen at base `d` fits every input up to `d ^ t` after `t` products. -/
private lemma ceilSide_le_pow {n d t : ℕ} (hn : 1 ≤ n) (hd : 1 ≤ d)
    (hnd : n ≤ d ^ t) {x : ℝ} (hx : 0 ≤ x) :
    ceilSide n hn x ≤ (ceilSide d hd x) ^ t := by
  change ⌈(n : ℝ) ^ x⌉₊ ≤ (⌈(d : ℝ) ^ x⌉₊) ^ t
  apply Nat.ceil_le.mpr
  rw [Nat.cast_pow]
  calc
    (n : ℝ) ^ x ≤ ((d : ℝ) ^ t) ^ x :=
      Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast hnd) hx
    _ = ((d : ℝ) ^ x) ^ t := (Real.rpow_pow_comm (Nat.cast_nonneg d) _ _).symm
    _ ≤ _ := pow_le_pow_left₀ (by positivity) (Nat.le_ceil _) t

/-- Each of the three ceilings contributes at most two to the spectral value. -/
private lemma eval_rounded_le (φ : Spectral F) {d : ℕ} (hd : 1 ≤ d) {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    PolMul.Spectral.eval φ (matMul (ceilSide d hd a) (ceilSide d hd b) (ceilSide d hd c)) ≤
      8 * (d : ℝ) ^ mmWeight φ a b c := by
  have side (x : ℝ) (hx : 0 ≤ x) (i : Fin 3) :
      ((ceilSide d hd x : ℕ) : ℝ) ^ theta φ i ≤ 2 * ((d : ℝ) ^ x) ^ theta φ i := by
    calc
      _ ≤ (2 * (d : ℝ) ^ x) ^ theta φ i :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) (ceil_rpow_le_two_mul hd hx) (theta_mem_Icc φ i).1
      _ = (2 : ℝ) ^ theta φ i * ((d : ℝ) ^ x) ^ theta φ i :=
        Real.mul_rpow (by norm_num) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right
        ((Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
          (theta_mem_Icc φ i).2).trans_eq (Real.rpow_one _)) (by positivity)
  rw [Omega.eval_matMul, rpow_mmWeight φ (by exact_mod_cast hd : 0 < (d : ℝ))]
  calc
    _ ≤ (2 * ((d : ℝ) ^ a) ^ theta φ 1) * (2 * ((d : ℝ) ^ b) ^ theta φ 2) *
          (2 * ((d : ℝ) ^ c) ^ theta φ 0) :=
      mul_le_mul (mul_le_mul (side a ha 1) (side b hb 2) (by positivity) (by positivity))
        (side c hc 0) (by positivity) (by positivity)
    _ = _ := by ring

private noncomputable abbrev roundedBlock (F : Type u) [Field F] (d : ℕ) (hd : 1 ≤ d)
    (a b c : ℝ) : TensorClass F 3 :=
  TensorClass.mk ⟨_, matMul (F := F) (ceilSide d hd a) (ceilSide d hd b) (ceilSide d hd c)⟩

/-- A strict asymptotic-rank bound for one block gives ordinary-rank bounds
at every input size. Adding the fixed threshold `K + 1` to the power cover
absorbs the initial powers into a single multiplicative constant. -/
private theorem rectAdmissible_of_block {d : ℕ} (hd : 1 < d) {a b c τ : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hτ : 0 ≤ τ)
    (hρ : (PolMul.OmegaBridge.pF F).asympRank (roundedBlock F d hd.le a b c) < (d : ℝ) ^ τ) :
    RectAdmissible F a b c τ := by
  let p := PolMul.OmegaBridge.pF F
  let T := roundedBlock F d hd.le a b c
  let D := (d : ℝ) ^ τ
  have hunit : p.rel 1 T := one_le_matMul_class _ _ _
  have hev : ∀ᶠ t : ℕ in Filter.atTop, (p.rank (T ^ t) : ℝ) ^ (1 / (t : ℝ)) < D :=
    (p.asympRank_eq_tendsto hunit).eventually_lt_const hρ
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 hev
  refine ⟨D ^ (K + 1), fun n hn => ?_⟩
  let l := Nat.log d n
  let t := l + (K + 1)
  have hKt : K ≤ t := by dsimp [t]; omega
  have ht : t ≠ 0 := by dsimp [t]; omega
  have hnt : n ≤ d ^ t :=
    (Nat.lt_pow_succ_log_self hd n).le.trans
      (Nat.pow_le_pow_right hd.le (show l + 1 ≤ t by dsimp [t]; omega))
  have hr := pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hK t hKt).le t
  rw [one_div, Real.rpow_inv_natCast_pow (Nat.cast_nonneg _) ht] at hr
  have hmono := tensorRank_matMul_mono (F := F) (ceilSide_le_pow hn hd.le hnt ha)
    (ceilSide_le_pow hn hd.le hnt hb) (ceilSide_le_pow hn hd.le hnt hc)
  have hfit : tensorRank (matMul (F := F) (ceilSide n hn a) (ceilSide n hn b) (ceilSide n hn c)) ≤
      p.rank (T ^ t) := by
    dsimp only [T, roundedBlock, p, PolMul.OmegaBridge.pF]
    rw [matMul_class_pow, strassenRank_mk_eq_tensorRank]
    exact hmono
  calc
    _ ≤ (p.rank (T ^ t) : ℝ) := by exact_mod_cast hfit
    _ ≤ D ^ t := hr
    _ = D ^ (K + 1) * D ^ l := by rw [show t = K + 1 + l by dsimp [t]; omega, pow_add]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) τ) _)
      rw [show D ^ l = ((d : ℝ) ^ l) ^ τ from Real.rpow_pow_comm (Nat.cast_nonneg d) _ _]
      have hlog : (d : ℝ) ^ l ≤ n := by exact_mod_cast Nat.pow_log_le_self d (show n ≠ 0 by omega)
      exact Real.rpow_le_rpow (by positivity) hlog hτ

/-- A uniform bound on the spectral weights bounds the rank-growth exponent.
For each larger exponent, choose the base large enough to absorb all three ceilings. -/
theorem omegaRect_le_of_mmWeight_le {a b c M : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hM : ∀ φ : Spectral F, mmWeight φ a b c ≤ M) : omegaRect F a b c ≤ M := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro τ hτ
  obtain ⟨d, hd⟩ := exists_nat_gt (max 1 ((8 : ℝ) ^ (τ - M)⁻¹))
  have hd1 : (1 : ℝ) < d := (le_max_left _ _).trans_lt hd
  have hdN : 1 < d := by exact_mod_cast hd1
  have hd0 := zero_lt_one.trans hd1
  have hlarge : 8 < (d : ℝ) ^ (τ - M) :=
    (Real.rpow_inv_lt_iff_of_pos (by norm_num) (Nat.cast_nonneg d) (sub_pos.mpr hτ)).mp
      ((le_max_right _ _).trans_lt hd)
  let p := PolMul.OmegaBridge.pF F
  let T := roundedBlock F d hdN.le a b c
  let _ : Nonempty (AsymptoticSpectrum p) := AsymptoticSpectrum.nonempty p
  have hunit : p.rel 1 T := one_le_matMul_class _ _ _
  have hone : ∃ φ : AsymptoticSpectrum p, 1 ≤ AsymptoticSpectrum.eval p T φ := by
    obtain ⟨φ⟩ := (inferInstance : Nonempty (AsymptoticSpectrum p))
    exact ⟨φ, (AsymptoticSpectrum.eval_one p φ).symm.le.trans (AsymptoticSpectrum.eval_mono p φ hunit)⟩
  obtain ⟨φ, hφ⟩ := p.asympRank_eq_max_spectrum T hone
  have hweight : 0 ≤ mmWeight φ a b c :=
    add_nonneg (add_nonneg (mul_nonneg ha (theta_mem_Icc φ 1).1) (mul_nonneg hb (theta_mem_Icc φ 2).1))
      (mul_nonneg hc (theta_mem_Icc φ 0).1)
  apply csInf_le (rectAdmissible_bddBelow F a b c)
  apply rectAdmissible_of_block hdN ha hb hc ((hweight.trans (hM φ)).trans hτ.le)
  calc
    p.asympRank T = AsymptoticSpectrum.eval p T φ := hφ
    _ ≤ 8 * (d : ℝ) ^ mmWeight φ a b c := eval_rounded_le φ hdN.le ha hb hc
    _ ≤ 8 * (d : ℝ) ^ M := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hd1.le (hM φ)) (by norm_num)
    _ < (d : ℝ) ^ τ := by
      have h := mul_lt_mul_of_pos_right hlarge (Real.rpow_pos_of_pos hd0 M)
      rwa [← Real.rpow_add hd0, sub_add_cancel] at h

/-- Strassen's rectangular maximum (AvdBZ, Lemma 4.4), including zero widths. -/
theorem omegaRect_isGreatest (F : Type u) [Field F] {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    IsGreatest (Set.range (fun φ : Spectral F => mmWeight φ a b c)) (omegaRect F a b c) := by
  obtain ⟨φ, hφ⟩ := exists_max_mmWeight F a b c
  refine ⟨⟨φ, le_antisymm (mmWeight_le_omegaRect φ ha hb hc)
    (omegaRect_le_of_mmWeight_le ha hb hc hφ)⟩, ?_⟩
  rintro _ ⟨ψ, rfl⟩
  exact mmWeight_le_omegaRect ψ ha hb hc

end OM.PolMulRect
