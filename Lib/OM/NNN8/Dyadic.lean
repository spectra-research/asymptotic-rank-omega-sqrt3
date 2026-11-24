import Lib.OM.NNN8.Rate
import Lib.OM.NNN2.Orientations
import Lib.OM.NNN.SpectralBound

/-! A uniform bound for every dyadic tensor and every spectral point.
Both the point and tensor are transported when choosing the largest orientation. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN8
open Semicontinuity OM.NNN.Raw Foundations.HyperbolicLift
  Foundations.PairUnitExponents Foundations.OrientationTransport
set_option maxHeartbeats 2000000

lemma maximum_parameter_caps (φ : PolMul.Spectral ℂ)
    (h0 : theta φ 0 ≤ theta φ 2) (h1 : theta φ 1 ≤ theta φ 2) :
    let t := max (3 / 4) (theta φ 2)
    t ∈ Set.Icc (3 / 4 : ℝ) 1 ∧ theta φ 2 ≤ t ∧
      theta φ 0 + theta φ 1 ≤ 9 / 4 - t := by
  dsimp only
  refine ⟨⟨le_max_left _ _, max_le (by norm_num) (theta_mem_Icc φ 2).2⟩,
    le_max_right _ _, ?_⟩
  by_cases ht : 3 / 4 ≤ theta φ 2
  · rw [max_eq_right ht]
    linarith [Omega.theta_sum_le_nine_quarters φ]
  · rw [max_eq_left (le_of_not_ge ht)]
    linarith

theorem third_dyadic_spectral (φ : PolMul.Spectral ℂ) (l : ℕ) (n : ℕ+)
    (hn : (n : ℕ) = 2 ^ l) (T : KTensor ℂ (fun _ : Fin 3 => n))
    (h0 : theta φ 0 ≤ theta φ 2) (h1 : theta φ 1 ≤ theta φ 2) :
    PolMul.Spectral.eval φ T ≤ 2 * (n : ℝ) ^ alpha0 := by
  let e : BinaryWord l ≃ Fin n := Fintype.equivOfCardEq (by simp [hn, binary_word_card])
  let S : CoordinateTensor.Cube ℂ (BinaryWord l) := fun a b c => T (idx3 (e a) (e b) (e c))
  have hv : value φ S = PolMul.Spectral.eval φ T :=
    (value_reindex φ (fun a b c => T (idx3 a b c)) e e e).trans (value_encode φ T)
  obtain ⟨ht, hb, ha⟩ := maximum_parameter_caps φ h0 h1
  have h := third_dyadic_value φ l S ht hb ha
  rw [hv] at h
  have hnR : (n : ℝ) = (2 : ℝ) ^ l := by exact_mod_cast hn
  rwa [hnR]

theorem dyadic_spectral (φ : PolMul.Spectral ℂ) (l : ℕ) (n : ℕ+)
    (hn : (n : ℕ) = 2 ^ l) (T : KTensor ℂ (fun _ : Fin 3 => n)) :
    PolMul.Spectral.eval φ T ≤ 2 * (n : ℝ) ^ alpha0 := by
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 3))
    (theta φ) Finset.univ_nonempty
  let σ := rot i
  let ψ := pullPoint φ σ
  let S : KTensor ℂ (fun _ : Fin 3 => n) := KTensor.legReindex σ T
  have ht (j : Fin 3) : theta ψ j = theta φ (σ.symm j) := theta_legReindex φ σ j
  have hmax (j : Fin 3) : theta ψ j ≤ theta ψ 2 := by
    rw [ht, ht, show σ.symm 2 = i from rot_symm_two i]
    exact hi _ (Finset.mem_univ _)
  have h := third_dyadic_spectral ψ l n hn S (hmax 0) (hmax 1)
  have hx : PolMul.Spectral.eval ψ S = PolMul.Spectral.eval φ T := by
    change AsymptoticSpectrumDuality.AsymptoticSpectrum.eval _
      (legPermEquiv σ (legPermEquiv σ (TensorClass.mk ⟨_, T⟩))) φ = _
    rw [legPermEquiv_rot_rot]
    rfl
  rwa [hx] at h

theorem dyadic_asympRank (l : ℕ) (n : ℕ+) (hn : (n : ℕ) = 2 ^ l)
    (T : KTensor ℂ (fun _ : Fin 3 => n)) :
    asympRank T ≤ 2 * (n : ℝ) ^ alpha0 := by
  exact OM.NNN.asympRank_le_of_spectral_bound T _ (by positivity)
    (fun φ => dyadic_spectral φ l n hn T)

end OM.NNN8
