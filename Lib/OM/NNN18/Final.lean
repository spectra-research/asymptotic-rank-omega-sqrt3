import Lib.OM.NNN18.FactsU
import Lib.OM.NNN18.FactsC
import Lib.OM.NNN8.Transfer
import Lib.OM.NNN.SpectralBound
import Lib.OM.NNN12.Profiles
import PLATFORM.Statements.«NNN.18»
import PLATFORM.Statements.«NNN.19»

/-!
At a spectral point, enlarge the edge exponents to an upper profile with sum `Ω`.  If some
`δ_i > R`, the coefficient star omitting edge `i` prices the cube at `2t - R = B` (10.1).
Otherwise the profile lies in the triangle, the three tariffs hold (`tariffs_valid`), and a focus
with `δ_h ≥ 0` prices the cube at `u + 2v + (2b-a)δ_h ≤ B` (3.3).  Dyadic padding of powers and
full-spectrum duality (the NNN.15 reduction) give every `n ≥ 1`.  The only open premise is the
packed network step `TriangleStep`.
-/

noncomputable section
open scoped BigOperators
open CoordinateTensor OM.NNN.Raw
open Semicontinuity Foundations.HyperbolicLift
open OM.NNN8 (BinaryWord binary_word_card)
open OM.NNN12 (Shape DyadicTensor)
namespace OM.NNN18

lemma cube_price (P : Track) (δ : Fin 3 → ℝ) (h : Fin 3) (l : ℝ) :
    NNN13.plane (tariff P δ h) (fun _ => l) = l * (P.u + 2 * P.v + (2 * P.b - P.a) * δ h) := by
  fin_cases h <;> simp [NNN13.plane, tariff, other] <;> ring

/-- The dyadic cube bound at one spectral point, given an upper profile with sum `3 t₀`. -/
theorem dyadic_cube (P : Track) (G : TrackFacts P) (TS : TriangleStep) {B : ℝ}
    (hB : 2 * (P.t : ℝ) - G.R = B) (hcube : (P.u : ℝ) + 2 * P.v ≤ B) (hab : 2 * (P.b : ℝ) ≤ P.a)
    (hΩ : 3 * (P.t : ℝ) ≤ 9 / 4)
    (φ : PolMul.Spectral ℂ) (t : Fin 3 → ℝ) (hθ : ∀ i, Foundations.PairUnitExponents.theta φ i ≤ t i)
    (hs : t 0 + t 1 + t 2 = 3 * P.t) (l : ℕ) (T : DyadicTensor (fun _ => l)) :
    value φ T ≤ (2 : ℝ) ^ (B * l) := by
  set δ : Fin 3 → ℝ := fun i => t i - P.t
  have htd : theta P δ = t := by funext i; simp [theta, δ]
  have hl : (0 : ℝ) ≤ l := Nat.cast_nonneg l
  by_cases hmax : ∀ i, δ i ≤ G.R
  · have hδ : InTri G.R δ := ⟨by simp only [δ]; linarith, hmax⟩
    have hθ' : ∀ i, Foundations.PairUnitExponents.theta φ i ≤ theta P δ i := by rw [htd]; exact hθ
    have hsum : ∑ i, theta P δ i ≤ 9 / 4 := by rw [htd, Fin.sum_univ_three]; linarith
    -- a focus with δ_h ≥ 0
    obtain ⟨h, hh⟩ : ∃ h, 0 ≤ δ h := by
      by_contra hc; push_neg at hc
      have := hδ.1; linarith [hc 0, hc 1, hc 2]
    have hv := tariffs_valid P G TS φ hδ hθ' hsum h (fun _ => l) T
    refine hv.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
    have e : NNN13.plane (tariff P δ h) (fun j => (((fun _ => l) : Shape) j : ℝ)) =
        (l : ℝ) * (P.u + 2 * P.v + (2 * P.b - P.a) * δ h) := cube_price P δ h l
    rw [e]
    have : (2 * (P.b : ℝ) - P.a) * δ h ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hh
    nlinarith
  · push_neg at hmax
    obtain ⟨i, hi⟩ := hmax
    have hv := star_affine φ t hθ i (fun _ => l) T
    refine hv.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
    have e : NNN13.plane (star t i) (fun j => (((fun _ => l) : Shape) j : ℝ)) =
        (l : ℝ) * (t 0 + t 1 + t 2 - t i) := by
      fin_cases i <;> simp [NNN13.plane, star, other] <;> ring
    rw [e]
    have : t 0 + t 1 + t 2 - t i ≤ B := by simp only [δ] at hi; linarith
    nlinarith

/-- The dyadic-to-every-dimension reduction of NNN.15 (powers, padding, duality). -/
theorem all_dims {β : ℝ} (hβ : 0 ≤ β)
    (hb : ∀ (φ : PolMul.Spectral ℂ) (l : ℕ) (T : DyadicTensor (fun _ => l)),
      value φ T ≤ (2 : ℝ) ^ (β * l))
    (n : ℕ+) (T : KTensor ℂ (fun _ : Fin 3 => n)) : asympRank T ≤ (n : ℝ) ^ β := by
  apply OM.NNN.asympRank_le_of_spectral_bound T _ (by positivity)
  intro φ
  apply NNN8.spectral_power_padding_transfer (a := β) (C := 1) hβ (by norm_num) _ φ n T
  intro ψ l N hN U
  rw [one_mul]
  let e : BinaryWord l ≃ Fin N := Fintype.equivOfCardEq (by simp [hN])
  let S : CoordinateTensor.Cube ℂ (BinaryWord l) := fun a b c => U (idx3 (e a) (e b) (e c))
  have hv : value ψ S = PolMul.Spectral.eval ψ U :=
    (value_reindex ψ (fun a b c => U (idx3 a b c)) e e e).trans (value_encode ψ U)
  have hb' := hb ψ l S
  rw [hv] at hb'
  have hnR : (N : ℝ) = (2 : ℝ) ^ l := by exact_mod_cast hN
  rw [hnR, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm]
  exact hb'

/-- **NNN.18 from the packed network step.** -/
theorem nnn18_of_triangleStep (TS : TriangleStep) : S_NNN_18 := by
  intro n T
  apply all_dims (by norm_num) _ n T
  intro φ l S
  obtain ⟨t, hθ, ht, hs⟩ := OM.NNN12.exists_spectral_parameters φ
  exact dyadic_cube U FactsU.facts TS (B := 139999 / 100000)
    (by simp only [FactsU.facts, FocusU.R, U]; norm_num) (by norm_num [U]) (by norm_num [U])
    (by norm_num [U]) φ t hθ (by rw [hs]; norm_num [U]) l S

/-- Under `ω = 2` every spectral point has `θ₀ + θ₁ + θ₂ ≤ 2` (`PolMul.SpectralFacts.proof_SP_1`). -/
lemma theta_sum_le_two (hω : OM.PolMul.omegaF ℂ = 2) (φ : PolMul.Spectral ℂ) :
    Foundations.PairUnitExponents.theta φ 0 + Foundations.PairUnitExponents.theta φ 1 +
      Foundations.PairUnitExponents.theta φ 2 ≤ 2 := by
  have h := (OM.PolMul.SpectralFacts.proof_SP_1 ℂ).2 ⟨φ, rfl⟩
  change Real.logb 2 (OM.PolMul.Spectral.eval φ (OM.PolMul.matMul 2 2 2)) ≤ OM.PolMul.omegaF ℂ at h
  rw [hω, OM.Omega.eval_matMul_square] at h
  simpa only [PNat.val_ofNat, Nat.cast_ofNat,
    Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)] using h

/-- Enlargement of the edge exponents to an upper profile with sum `2`. -/
lemma exists_profile_two (hω : OM.PolMul.omegaF ℂ = 2) (φ : PolMul.Spectral ℂ) :
    ∃ t : Fin 3 → ℝ, (∀ i, Foundations.PairUnitExponents.theta φ i ≤ t i) ∧ t 0 + t 1 + t 2 = 2 := by
  set θ := Foundations.PairUnitExponents.theta φ
  have hs := theta_sum_le_two hω φ
  have hm : ∀ i, θ i ∈ Set.Icc (0 : ℝ) 1 := fun i => Foundations.PairUnitExponents.theta_mem_Icc φ i
  set s := θ 0 + θ 1 + θ 2
  have hd : 0 < 3 - s := by linarith
  set q := (2 - s) / (3 - s)
  refine ⟨fun i => θ i + q * (1 - θ i), fun i => ?_, ?_⟩
  · have hq : 0 ≤ q := div_nonneg (by linarith) hd.le
    have := (hm i).2
    nlinarith
  · have : q * (3 - s) = 2 - s := div_mul_cancel₀ _ hd.ne'
    simp only [s] at this ⊢
    nlinarith

/-- **NNN.19 from the packed network step.** -/
theorem nnn19_of_triangleStep (TS : TriangleStep) : S_NNN_19 := by
  intro hω n T
  apply all_dims (by norm_num) _ n T
  intro φ l S
  obtain ⟨t, hθ, hs⟩ := exists_profile_two hω φ
  exact dyadic_cube C FactsC.facts TS (B := 12499 / 10000)
    (by simp only [FactsC.facts, FocusC.R, C]; norm_num) (by norm_num [C]) (by norm_num [C])
    (by norm_num [C]) φ t hθ (by rw [hs]; norm_num [C]) l S

end OM.NNN18
