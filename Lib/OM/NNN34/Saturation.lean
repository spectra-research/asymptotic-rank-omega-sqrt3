import Lib.OM.NNN34.PartitionGrowth
import Lib.OM.NNN34.RelativePrice
import Lib.OM.NNN34.Rectangle
import Lib.OM.NNN32.Conclusion
import Lib.OM.NNN32.Implication
import PLATFORM.Statements.«R114.19»
import PLATFORM.Statements.«R114.21»
import PLATFORM.Statements.«R114.22»
import PLATFORM.Statements.«R114.25»
import PLATFORM.Statements.«NNN.34»
import PLATFORM.Statements.«NNN.35»

/-! # Saturation of the two partition witnesses and the final exponent implications -/

namespace OM.NNN34

open Filter Topology P2M.R114 Semicontinuity

private lemma saturates {L N : ℕ → ℝ} {q : ℝ} (hq : 0 < q)
    (hL : ∀ᶠ H in atTop, 0 ≤ L H ∧ L H ≤ q)
    (hN : ∀ᶠ H in atTop, N H ≤ q)
    (hs : ∀ b, 0 ≤ b → (∀ M, ∃ H ≥ max 2 M, L H ≤ b ∧ N H ≤ q) → q ≤ (b+q)/2) :
    Tendsto L atTop (𝓝 q) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    by_contra he
    have hf : ∃ᶠ H in atTop, ¬ a < L H := not_eventually.mp he
    have hc : ∀ M, ∃ H ≥ max 2 M, L H ≤ max 0 a ∧ N H ≤ q := by
      intro M
      obtain ⟨H, hH, hh, hN'⟩ := frequently_atTop.mp (hf.and_eventually hN) (max 2 M)
      exact ⟨H,hH,(le_of_not_gt hh).trans (le_max_right _ _),hN'⟩
    have h := hs _ (le_max_left _ _) hc
    linarith [max_lt hq ha]
  · intro b hb
    exact hL.mono fun _ h => h.2.trans_lt hb

private theorem sides_large : ∀ᶠ H in atTop, 2 ≤ partitionSide H := by
  filter_upwards [proof_R114_13.1.eventually_ge_atTop 2] with H h
  exact h

theorem saturation_of_plane (plane : S_R114_19) : S_R114_21 := by
  intro hg
  let q := 1/Real.sqrt 3
  have hq : 0 < q := by dsimp [q]; positivity
  have bounds (T : (H : ℕ) → KTensor ℂ (fun _ : Fin 3 => partitionSide H)) :
      ∀ᶠ H in atTop, 0 ≤ relativeCost (T H) ∧ relativeCost (T H) ≤ q := by
    filter_upwards [sides_large] with H hh
    have h := proof_R114_14 _ (T H) hh
    exact ⟨h.1,h.2.1⟩
  have hL := bounds leftFactor
  have hN := bounds rightFactor
  constructor
  · apply saturates hq hL (hN.mono fun _ h => h.2)
    intro b hb hc
    exact proof_R114_20 b q hb hq.le (plane hg b q hb hq.le hc)
  · apply saturates hq hN (hL.mono fun _ h => h.2)
    intro b hb hc
    have h := proof_R114_20 q b hq.le hb (plane hg q b hq.le hb fun M => by
      obtain ⟨H,hH,hN',hL'⟩ := hc M
      exact ⟨H,hH,hL',hN'⟩)
    simpa only [add_comm] using h

theorem rank_witness_of_saturation (coeffs : S_R114_21) : S_R114_22 := by
  intro hg ε hε
  let q := 1/Real.sqrt 3
  have hq : 0 < q := by dsimp [q]; positivity
  have witness (T : (H : ℕ) → KTensor ℂ (fun _ : Fin 3 => partitionSide H))
      (hc : Tendsto (fun H => relativeCost (T H)) atTop (𝓝 q)) :
      ∀ᶠ H in atTop, ((partitionSide H : ℕ) : ℝ)^(2/Real.sqrt 3-ε) ≤ asympRank (T H) := by
    filter_upwards [sides_large, hc.eventually (Ioi_mem_nhds hq),
      hc.eventually (Ioi_mem_nhds (show q-ε/2 < q by linarith))] with H hD hpos hcoeff
    have hn : T H ≠ 0 := by
      intro hz
      change 0 < relativeCost (T H) at hpos
      simp [relativeCost, hz] at hpos
    obtain ⟨φ,_⟩ := (PolMul.SpectralFacts.proof_SP_1 ℂ).1
    have hR := (PolMul.SpectralFacts.proof_SP_4 ℂ φ (T H) hn).trans (spectral_le_concrete φ (T H))
    have hb := (proof_R114_14 _ (T H) hD).2.2 hn
    apply (Real.le_logb_iff_rpow_le (by exact_mod_cast (show 1 < (partitionSide H : ℕ) from hD))
      (zero_lt_one.trans_le hR)).1
    change q-ε/2 < relativeCost (T H) at hcoeff
    apply le_trans _ hb
    change 1 / Real.sqrt 3 - ε/2 < relativeCost (T H) at hcoeff
    calc
      _ = 2*(1/Real.sqrt 3-ε/2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hcoeff.le (by norm_num)
  exact (witness leftFactor (coeffs hg).1).and (witness rightFactor (coeffs hg).2)

theorem upper_case_of_witness (hw : S_R114_22) : S_R114_25 := by
  intro hg
  by_contra! hb
  let ε := (2/Real.sqrt 3-beta)/2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨H,hH,hD⟩ := ((hw hg ε hε).and sides_large).exists
  have h := hH.1.trans ((proof_R114_23 beta).1 le_rfl _ (leftFactor H))
  have he := (Real.rpow_le_rpow_left_iff
    (by exact_mod_cast (show 1 < (partitionSide H : ℕ) from hD))).mp h
  dsimp [ε] at he
  linarith

theorem dichotomy_of_upper_case (high : S_R114_25) : S_NNN_34 := by
  have sep : PolMul.omegaF ℂ / 2 < 2 / Real.sqrt 3 := by
    have hh : 0 < Real.sqrt 3 := by positivity
    have hsq : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
    have hnum : 9/8 < 2/Real.sqrt 3 := by
      rw [lt_div_iff₀ hh]
      nlinarith only [hsq, sq_nonneg (Real.sqrt 3 - 16/9)]
    exact lt_of_le_of_lt (by linarith [Omega.omega_le_nine_quarters (F := ℂ)]) hnum
  have second (hn : P2M.R113.gamma ≠ 1) := high (NNN32.proof_R113_22.1.resolve_left hn)
  refine ⟨⟨?_, ?_⟩, fun hn => ⟨second hn,proof_R114_24.2⟩⟩
  · intro he
    by_contra hn
    linarith [second hn]
  · intro hg
    exact le_antisymm ((proof_R114_23 _).2 (NNN32.proof_R113_12 (NNN32.proof_R113_23.mp hg)))
      proof_R114_24.1

theorem conjecture_of_dichotomy (h : S_NNN_34) : S_NNN_35 := by
  intro hω
  have low := h.1
  have hβ := proof_R114_24.1
  rw [hω] at low hβ
  norm_num at low hβ
  constructor
  · intro hc
    apply low.mp
    refine le_antisymm ((proof_R114_23 1).2 ?_) hβ
    simpa using hc
  · intro hg n T
    simpa using (proof_R114_23 1).1 (low.mpr hg).le n T

end OM.NNN34
