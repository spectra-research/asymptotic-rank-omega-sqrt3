import Lib.OM.PolMul.Main
import Lib.OM.MatrixDiagonal
import Foundations.Tensors.AsympRankBridge
import Foundations.Tensors.PairUnitExponents

/-!
The nine-quarters bound in Foundations's tensor framework.

`PolMul.Main` ports the complete polynomial-multiplication proof, using the
existing Foundations tensor semiring throughout. This module identifies
its matrix-multiplication factors with the oriented pair units used by the
universal-bound proofs and passes from spectral values to `asympRank`.
-/

namespace OM.Omega

open Semicontinuity AsymptoticSpectrumDuality
open AsymptoticSpectrumDuality.AsymptoticSpectrum
open Foundations.PairUnitExponents

universe u
variable {F : Type u} [Field F]

/-- The usual size-based matrix-multiplication exponent, over any field. -/
theorem omega_le_nine_quarters : PolMul.omegaF F ≤ (9 : ℝ) / 4 :=
  PolMul.Main.proof_MAIN_1 F

lemma eval_matMul_n11 (φ : PolMul.Spectral F) (n : ℕ+) :
    PolMul.Spectral.eval φ (PolMul.matMul n 1 1) =
      ((n : ℕ) : ℝ) ^ theta φ 1 := by
  let ψ := ofAbstractSpectralPoint (K := F) (k := 3) (by norm_num) φ
  have h := PolMul.SpectralFacts.eval_matMul_n11_eq_pair ψ n
  change PolMul.Spectral.eval φ (PolMul.matMul n 1 1) = _ at h
  rw [h, ← eval_orientedPairUnit_eq_rpow φ 1 n n.pos]
  rw [orientedPairUnit, pairUnitTT_complementary_eq 1 n n.pos]
  rfl

lemma eval_matMul_1n1 (φ : PolMul.Spectral F) (n : ℕ+) :
    PolMul.Spectral.eval φ (PolMul.matMul 1 n 1) =
      ((n : ℕ) : ℝ) ^ theta φ 2 := by
  let ψ := ofAbstractSpectralPoint (K := F) (k := 3) (by norm_num) φ
  have h := PolMul.SpectralFacts.eval_matMul_1n1_eq_pair ψ n
  change PolMul.Spectral.eval φ (PolMul.matMul 1 n 1) = _ at h
  rw [h, ← eval_orientedPairUnit_eq_rpow φ 2 n n.pos]
  rw [orientedPairUnit, pairUnitTT_complementary_eq 2 n n.pos]
  rfl

lemma eval_matMul_11n (φ : PolMul.Spectral F) (n : ℕ+) :
    PolMul.Spectral.eval φ (PolMul.matMul 1 1 n) =
      ((n : ℕ) : ℝ) ^ theta φ 0 := by
  let ψ := ofAbstractSpectralPoint (K := F) (k := 3) (by norm_num) φ
  have h := PolMul.SpectralFacts.eval_matMul_11n_eq_pair ψ n
  change PolMul.Spectral.eval φ (PolMul.matMul 1 1 n) = _ at h
  rw [h, ← eval_orientedPairUnit_eq_rpow φ 0 n n.pos]
  rw [orientedPairUnit, pairUnitTT_complementary_eq 0 n n.pos]
  rfl

/-- Rectangular matrix multiplication in the universal proofs' orientation convention. -/
theorem eval_matMul (φ : PolMul.Spectral F) (a b c : ℕ+) :
    PolMul.Spectral.eval φ (PolMul.matMul a b c) =
      ((a : ℕ) : ℝ) ^ theta φ 1 * ((b : ℕ) : ℝ) ^ theta φ 2 *
        ((c : ℕ) : ℝ) ^ theta φ 0 := by
  have h := PolMul.SpectralFacts.eval_matMul_factor
    (ofAbstractSpectralPoint (K := F) (k := 3) (by norm_num) φ) a b c
  change PolMul.Spectral.eval φ (PolMul.matMul a b c) =
    PolMul.Spectral.eval φ (PolMul.matMul a 1 1) *
    PolMul.Spectral.eval φ (PolMul.matMul 1 b 1) *
    PolMul.Spectral.eval φ (PolMul.matMul 1 1 c) at h
  rw [h, eval_matMul_n11, eval_matMul_1n1, eval_matMul_11n]

theorem eval_matMul_square (φ : PolMul.Spectral F) (n : ℕ+) :
    PolMul.Spectral.eval φ (PolMul.matMul n n n) =
      ((n : ℕ) : ℝ) ^ (theta φ 0 + theta φ 1 + theta φ 2) := by
  have hn : (0 : ℝ) < ((n : ℕ) : ℝ) := by exact_mod_cast n.pos
  rw [eval_matMul, ← Real.rpow_add hn, ← Real.rpow_add hn]
  congr 1
  ring

/-- The exponent-sum upper bound needed by the universal estimates. -/
theorem theta_sum_le_nine_quarters (φ : PolMul.Spectral F) :
    theta φ 0 + theta φ 1 + theta φ 2 ≤ (9 : ℝ) / 4 := by
  have h := PolMul.Main.spectral_value_le φ
  rw [eval_matMul_square] at h
  simpa only [PNat.val_ofNat, Nat.cast_ofNat,
    Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)] using! h

/-- At least one of the three pair orientations has exponent at most `3/4`. -/
theorem exists_orientation_le_three_quarters (φ : PolMul.Spectral F) :
    ∃ i : Fin 3, theta φ i ≤ (3 : ℝ) / 4 := by
  by_contra h
  push_neg at h
  have hsum := theta_sum_le_nine_quarters φ
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  linarith

/-- Square matrix multiplication has asymptotic rank at most `n^(9/4)`.
The left side is exactly Foundations's concrete asymptotic rank. -/
theorem asympRank_matMul_le (n : ℕ+) :
    asympRank (PolMul.matMul (F := F) n n n) ≤
      ((n : ℕ) : ℝ) ^ ((9 : ℝ) / 4) := by
  let p := tensorStrassenPreorder (F := F) (k := 3) (by norm_num)
  let T : TensorClass F 3 := TensorClass.mk ⟨_, PolMul.matMul (F := F) n n n⟩
  haveI : Nontrivial (TensorClass F 3) := by
    refine ⟨1, 0, ?_⟩
    intro h
    apply p.not_rel_one_zero
    rw [h]
    exact p.refl 0
  letI : Nonempty (AsymptoticSpectrum p) := AsymptoticSpectrum.nonempty p
  have hn : (1 : ℝ) ≤ ((n : ℕ) : ℝ) := by exact_mod_cast n.pos
  have ha : ∃ φ : AsymptoticSpectrum p, 1 ≤ eval p T φ := by
    obtain ⟨φ⟩ := (inferInstance : Nonempty (AsymptoticSpectrum p))
    refine ⟨φ, ?_⟩
    change 1 ≤ PolMul.Spectral.eval φ (PolMul.matMul n n n)
    rw [eval_matMul_square]
    exact Real.one_le_rpow hn (by
      have h0 := (theta_mem_Icc φ 0).1
      have h1 := (theta_mem_Icc φ 1).1
      have h2 := (theta_mem_Icc φ 2).1
      linarith)
  obtain ⟨φ, hφ⟩ := p.asympRank_eq_max_spectrum T ha
  refine (Foundations.AsympRankBridge.asympRank_le_strassen (by norm_num) _).trans ?_
  change p.asympRank T ≤ _
  rw [hφ]
  change PolMul.Spectral.eval φ (PolMul.matMul n n n) ≤ _
  rw [eval_matMul_square]
  exact Real.rpow_le_rpow_of_exponent_le hn (theta_sum_le_nine_quarters φ)

end OM.Omega

namespace Foundations.PairUnitExponents

open OM AsymptoticSpectrumDuality

/-- The diagonal in ⟨n,n,2n⟩ forces the sum of the three pair exponents to be at least two. -/
theorem two_le_theta_sum {F : Type*} [Field F] [Infinite F] (φ : PolMul.Spectral F) :
    2 ≤ theta φ 0 + theta φ 1 + theta φ 2 := by
  let e := theta φ 0 + theta φ 1 + theta φ 2
  have bound (n : ℕ+) : ((n : ℕ) : ℝ) ^ (2-e) ≤ 2 ^ theta φ 0 := by
    have hn : (0 : ℝ) < (n : ℕ) := by exact_mod_cast n.pos
    have h := PolMul.square_le_eval_matMul φ n
    rw [Omega.eval_matMul, PNat.add_coe, Nat.cast_add, ← two_mul,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hn.le] at h
    rw [Real.rpow_sub hn, div_le_iff₀ (Real.rpow_pos_of_pos hn _), Real.rpow_two]
    simpa only [e, Real.rpow_add hn, mul_comm, mul_left_comm, mul_assoc] using h
  by_contra! h
  have grow : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (2-e)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr h)).comp tendsto_natCast_atTop_atTop
  obtain ⟨n, hn, hlarge⟩ := ((Filter.eventually_gt_atTop (0 : ℕ)).and
    (grow.eventually_gt_atTop (2 ^ theta φ 0))).exists
  exact (bound ⟨n, hn⟩).not_gt hlarge

end Foundations.PairUnitExponents
