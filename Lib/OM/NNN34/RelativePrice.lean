import Lib.OM.NNN34.CubeRanks
import PLATFORM.Statements.«R114.14»
import PLATFORM.Statements.«R114.15»

/-! # Pointwise cube prices and asymptotic triangle comparison -/

noncomputable section

namespace OM.NNN34

open Semicontinuity PolMul P2M.R114 Foundations.PairUnitExponents
open NNN.Raw CoordinateTensor Foundations.HyperbolicLift NNN8

private abbrev triangle := matMul (F := ℂ) 2 2 2
private abbrev tariff (φ : Spectral ℂ) := Real.logb 2 (φ.eval triangle)

private theorem tariff_eq (φ : Spectral ℂ) : tariff φ = theta φ 0 + theta φ 1 + theta φ 2 := by
  rw [tariff, triangle, Omega.eval_matMul_square]
  simp only [PNat.val_ofNat, Nat.cast_ofNat, Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)]

private theorem tariff_ge (φ : Spectral ℂ) : 2 ≤ tariff φ := tariff_eq φ ▸ two_le_theta_sum φ

/-- A dyadic cube bound for a fixed spectral point extends to all sides by padding its powers. -/
private theorem pointwise_padding (φ : Spectral ℂ) {a : ℝ} (ha : 0 ≤ a) (hb : NNN20.CubeBound a φ)
    (n : ℕ+) (T : KTensor ℂ (fun _ : Fin 3 => n)) : φ.eval T ≤ (n : ℝ) ^ a := by
  have hn : (0 : ℝ) < n := by positivity
  have hnp := Real.rpow_pos_of_pos hn a
  have hpow (k : ℕ) : (φ.eval T) ^ k ≤ 2 ^ a * ((n : ℝ) ^ a) ^ k := by
    let l := Nat.log 2 ((n : ℕ)^k) + 1
    let N : ℕ+ := ⟨2^l, by positivity⟩
    have hsize : (n : ℕ)^k ≤ (N : ℕ) :=
      (Nat.lt_pow_succ_log_self one_lt_two ((n : ℕ)^k)).le
    have hupper : (N : ℕ) ≤ 2*(n : ℕ)^k := by
      dsimp [N, l]; rw [pow_succ, mul_comm]
      exact Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 (pow_ne_zero k n.ne_zero))
    have hpad : ∀ i : Fin 3, ((fun _ : Fin 3 => n^k) i : ℕ) ≤ ((fun _ => N) i : ℕ) := by
      intro i; simpa using! hsize
    let S := kronPow T k
    let U := reembed hpad S
    let e : BinaryWord l ≃ Fin N := Fintype.equivOfCardEq (by simp [N])
    let X : CoordinateTensor.Cube ℂ (BinaryWord l) := fun a b c => U (idx3 (e a) (e b) (e c))
    have hv : value φ X = φ.eval U :=
      (value_reindex φ (fun i j k => U (idx3 i j k)) e e e).trans (value_encode φ U)
    have hdyadic := hb l X
    rw [hv] at hdyadic
    have hm := PolMul.Superadditivity.eval_restricts φ (reembed_restricts_to hpad S)
    have he : φ.eval S = (φ.eval T)^k := eval_kronPow φ T k
    rw [he] at hm
    have hN : (N : ℝ) = (2 : ℝ)^l := by change (((2^l : ℕ) : ℝ)) = _; norm_cast
    calc
      _ ≤ φ.eval U := hm
      _ ≤ (2 : ℝ)^(a*l) := hdyadic
      _ = (N : ℝ)^a := by rw [hN, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm]
      _ ≤ (2*(n : ℝ)^k)^a := Real.rpow_le_rpow (by positivity) (by exact_mod_cast hupper) ha
      _ = 2^a*((n : ℝ)^a)^k := by
        rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast,
          ← Real.rpow_mul hn.le, ← Real.rpow_natCast, ← Real.rpow_mul hn.le, mul_comm (k : ℝ) a]
  by_contra! h
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ((2 : ℝ)^a) ((one_lt_div hnp).mpr h)
  rw [div_pow, lt_div_iff₀ (pow_pos hnp k)] at hk
  exact (not_lt_of_ge (hpow k)) hk

private theorem pointwise_bound (φ : Spectral ℂ) (D : ℕ+) (U : KTensor ℂ (fun _ : Fin 3 => D)) :
    φ.eval U ≤ (D : ℝ) ^ (tariff φ / Real.sqrt 3) := by
  have hs : 0 < Real.sqrt 3 := by positivity
  apply pointwise_padding φ (div_nonneg (by linarith [tariff_ge φ]) hs.le)
  apply NNN22.cubeBound_of_Fv
  rw [le_div_iff₀ hs, mul_comm, tariff_eq]
  exact NNN30.proof_R111_3 φ

private abbrev ratio {D : ℕ+} (U : KTensor ℂ (fun _ : Fin 3 => D)) (φ : Spectral ℂ) :=
  Real.logb 2 (φ.eval U) / (Real.logb 2 (D : ℝ) * tariff φ)

private theorem side_log_pos {D : ℕ+} (hD : 2 ≤ D) : 0 < Real.logb 2 (D : ℝ) := by
  apply Real.logb_pos one_lt_two
  exact_mod_cast (show 1 < (D : ℕ) from hD)

private theorem ratio_bounds {D : ℕ+} (hD : 2 ≤ D) {U : KTensor ℂ (fun _ : Fin 3 => D)}
    (hu : U ≠ 0) (φ : Spectral ℂ) :
    0 ≤ ratio U φ ∧ ratio U φ ≤ 1 / Real.sqrt 3 ∧
      ratio U φ ≤ Real.logb (D : ℝ) (asympRank U) / 2 := by
  have hφ := PolMul.SpectralFacts.proof_SP_4 ℂ φ U hu
  have hφp := zero_lt_one.trans_le hφ
  have hcost := tariff_ge φ
  have ht : 0 < tariff φ := by linarith
  have hside := side_log_pos hD
  have hden := mul_pos hside ht
  have hlog := Real.logb_nonneg one_lt_two hφ
  refine ⟨div_nonneg hlog hden.le, (div_le_iff₀ hden).2 ?_, (div_le_iff₀ hden).2 ?_⟩
  · have h := (Real.logb_le_logb one_lt_two hφp (Real.rpow_pos_of_pos (by positivity) _)).mpr
      (pointwise_bound φ D U)
    rw [Real.logb_rpow_eq_mul_logb_of_pos (by positivity)] at h
    exact h.trans_eq (by ring)
  · have hb : 1 ≤ asympRank U := hφ.trans (spectral_le_concrete φ U)
    have he := (Real.logb_le_logb one_lt_two hφp (zero_lt_one.trans_le hb)).mpr
      (spectral_le_concrete φ U)
    have hDb : 1 < (D : ℝ) := by exact_mod_cast (show 1 < (D : ℕ) from hD)
    have heq : Real.logb 2 (D : ℝ) * Real.logb (D : ℝ) (asympRank U) =
        Real.logb 2 (asympRank U) := Real.mul_logb (by positivity) hDb.ne' (by linarith)
    have hpos := Real.logb_nonneg hDb hb
    refine he.trans (heq.symm.trans_le ?_)
    nlinarith only [mul_nonneg (mul_nonneg hside.le hpos) (sub_nonneg.mpr hcost)]

theorem proof_R114_14 : S_R114_14 := by
  intro D U hD
  classical
  by_cases hu : U = 0
  · simp [relativeCost, hu, Real.sqrt_nonneg]
  have hne : ¬ (D < 2 ∨ U = 0) := not_or.mpr ⟨not_lt.mpr hD, hu⟩
  have hb : BddAbove (Set.range (ratio U)) :=
    ⟨_, by rintro _ ⟨φ,rfl⟩; exact (ratio_bounds hD hu φ).2.1⟩
  obtain ⟨φ, _⟩ := (PolMul.SpectralFacts.proof_SP_1 ℂ).1
  have hn : (Set.range (ratio U)).Nonempty := ⟨_,φ,rfl⟩
  simp only [relativeCost, if_neg hne]
  change 0 ≤ sSup (Set.range (ratio U)) ∧ _ ∧ _
  refine ⟨(ratio_bounds hD hu φ).1.trans (le_csSup hb ⟨φ,rfl⟩),
    csSup_le hn (by rintro _ ⟨ψ,rfl⟩; exact (ratio_bounds hD hu ψ).2.1), fun _ => ?_⟩
  have h := csSup_le hn (by rintro _ ⟨ψ,rfl⟩; exact (ratio_bounds hD hu ψ).2.2)
  change 2 * sSup (Set.range (ratio U)) ≤ _
  linarith

theorem proof_R114_15 : S_R114_15 := by
  intro D U hD k l hk _ hl
  classical
  apply ((PolMul.OmegaBridge.pF ℂ).asympRel_iff_forall_spectrum _ _).mpr
  intro φ
  change Spectral ℂ at φ
  change φ.eval (kronPow U k) ≤ φ.eval (kronPow triangle l)
  rw [eval_kronPow, eval_kronPow]
  by_cases hu : U = 0
  · have hz : φ.eval (0 : KTensor ℂ (fun _ : Fin 3 => D)) = 0 := (PolMul.SpectralFacts.proof_SP_3 ℂ φ).1 _
    rw [hu, hz, zero_pow hk.ne']
    exact pow_nonneg (PolMul.Superadditivity.eval_nonneg φ _) _
  have ht : 0 < tariff φ := by linarith [tariff_ge φ]
  have hs := side_log_pos hD
  have hφ := PolMul.SpectralFacts.proof_SP_4 ℂ φ U hu
  have hb : BddAbove (Set.range (ratio U)) :=
    ⟨_, by rintro _ ⟨ψ,rfl⟩; exact (ratio_bounds hD hu ψ).2.1⟩
  have hupp : ratio U φ ≤ relativeCost U := by
    simp only [relativeCost, if_neg (not_or.mpr ⟨not_lt.mpr hD, hu⟩)]
    exact le_csSup hb ⟨φ,rfl⟩
  have h := (div_le_iff₀ (mul_pos hs ht)).mp hupp
  have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
  have h' := (lt_div_iff₀ hk').mp hl
  have htensor : 0 < φ.eval triangle := by
    rw [triangle, Omega.eval_matMul_square]; positivity
  apply (Real.logb_le_logb one_lt_two (pow_pos (zero_lt_one.trans_le hφ) _) (pow_pos htensor _)).mp
  rw [Real.logb_pow, Real.logb_pow]
  change _ ≤ (l : ℝ) * tariff φ
  calc
    _ ≤ (k : ℝ) * (relativeCost U * (Real.logb 2 (D : ℝ) * tariff φ)) :=
      mul_le_mul_of_nonneg_left h hk'.le
    _ = (relativeCost U * Real.logb 2 (D : ℝ) * k) * tariff φ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right h'.le ht.le

end OM.NNN34

