import Lib.OM.Omega
import Lib.OM.NNN.Monotonicity

namespace OM.NNN

open Semicontinuity AsymptoticSpectrumDuality
open AsymptoticSpectrumDuality.AsymptoticSpectrum

universe u
variable {F : Type u} [Field F]

/-- Transfer a uniform spectral bound to the concrete asymptotic rank,
including the zero tensor. -/
theorem asympRank_le_of_spectral_bound {d : Fin 3 → ℕ+} (T : KTensor F d)
    (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ φ : PolMul.Spectral F, PolMul.Spectral.eval φ T ≤ c) :
    asympRank T ≤ c := by
  by_cases hT : T = 0
  · simpa only [hT, asympRank_zero] using! hc
  let p := tensorStrassenPreorder (F := F) (k := 3) (by norm_num)
  let a : TensorClass F 3 := TensorClass.mk ⟨d, T⟩
  have hclass : a ≠ 0 := by
    intro ha
    have hrank : tensorRank T = 0 := by
      rw [← PolMul.OmegaBridge.strassenRank_mk_eq_tensorRank]
      change p.rank a = 0
      rw [ha]
      exact p.rank_natCast 0
    exact hT ((PolMul.OmegaBridge.tensorRank_eq_zero_iff T).mp hrank)
  have hunit : p.rel 1 a := by
    rw [TensorClass.one_def]
    exact unitTensor_one_restricts_of_ne_zero T hclass
  haveI : Nontrivial (TensorClass F 3) := by
    refine ⟨1, 0, ?_⟩
    intro he
    apply p.not_rel_one_zero
    rw [he]
    exact p.refl 0
  letI : Nonempty (AsymptoticSpectrum p) := AsymptoticSpectrum.nonempty p
  have ha : ∃ φ : AsymptoticSpectrum p, 1 ≤ eval p a φ := by
    obtain ⟨φ⟩ := (inferInstance : Nonempty (AsymptoticSpectrum p))
    refine ⟨φ, ?_⟩
    simpa only [eval_one] using! eval_mono p φ hunit
  obtain ⟨φ, hφ⟩ := p.asympRank_eq_max_spectrum a ha
  refine (Foundations.AsympRankBridge.asympRank_le_strassen (by norm_num) T).trans ?_
  change p.asympRank a ≤ c
  rw [hφ]
  exact h φ

/-- The simultaneous-block spectral inequality and the partition envelope bounds give
a linear saving in asymptotic rank for `n ≥ 7`. -/
theorem asympRank_linear_saving_of_envelopes (n : ℕ+) (hn : 7 ≤ (n : ℕ))
    (T : KTensor F (fun _ : Fin 3 => n))
    (h : ∀ (φ : PolMul.Spectral F) (p : List ℕ),
      p.sum = (n : ℕ) → (∀ a ∈ p, 7 ≤ a ∧ a ≤ 16) →
      (PolMul.Spectral.eval φ T) ^ 2 ≤
        squaredEnvelope n p (min (Foundations.PairUnitExponents.theta φ 0)
          (min (Foundations.PairUnitExponents.theta φ 1) (Foundations.PairUnitExponents.theta φ 2)))) :
    asympRank T ≤ ((n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) - 21 / 100 * ((n : ℕ) : ℝ) := by
  apply asympRank_le_of_spectral_bound T _
  · have hnR : (7 : ℝ) ≤ ((n : ℕ) : ℝ) := by exact_mod_cast hn
    have hn1 : (1 : ℝ) ≤ ((n : ℕ) : ℝ) := by linarith
    have hr := Real.rpow_le_rpow_of_exponent_le hn1
      (show (1 : ℝ) ≤ 3 / 2 by norm_num)
    rw [Real.rpow_one] at hr
    linarith
  · intro φ
    apply linear_saving_of_partition_envelopes n hn (PolMul.Spectral.eval φ T)
    intro p hsum hp
    let u := min (Foundations.PairUnitExponents.theta φ 0)
      (min (Foundations.PairUnitExponents.theta φ 1) (Foundations.PairUnitExponents.theta φ 2))
    refine ⟨u, ⟨?_, ?_⟩, h φ p hsum hp⟩
    · exact le_min (Foundations.PairUnitExponents.theta_mem_Icc φ 0).1
        (le_min (Foundations.PairUnitExponents.theta_mem_Icc φ 1).1
          (Foundations.PairUnitExponents.theta_mem_Icc φ 2).1)
    · obtain ⟨i, hi⟩ := Omega.exists_orientation_le_three_quarters φ
      fin_cases i
      · exact (min_le_left _ _).trans hi
      · exact ((min_le_right _ _).trans (min_le_left _ _)).trans hi
      · exact ((min_le_right _ _).trans (min_le_right _ _)).trans hi

end OM.NNN
