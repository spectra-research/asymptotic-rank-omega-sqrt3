import Lib.OM.NNN22.Rect
import Lib.OM.NNN20.Assembly
import Lib.OM.NNN18.Final
import PLATFORM.Statements.«R88.17»
import PLATFORM.Statements.«R88.18»

noncomputable section
open scoped BigOperators Classical

namespace OM.NNN22

open Foundations.PairUnitExponents

set_option maxHeartbeats 1000000

lemma Fv_eq : P2M.R88.Fv = OM.NNN22.Fv := rfl

/-- Relabel so that the actual pair exponents, not merely an upper profile, are sorted. -/
lemma exists_sorted_theta (φ : PolMul.Spectral ℂ) :
    ∃ ψ, OM.NNN20.Reach φ ψ ∧ theta ψ 1 ≤ theta ψ 0 ∧ theta ψ 2 ≤ theta ψ 1 ∧
      theta ψ 0 + theta ψ 1 + theta ψ 2 = theta φ 0 + theta φ 1 + theta φ 2 := by
  rcases le_total (theta φ 1) (theta φ 0) with h01 | h10 <;>
    rcases le_total (theta φ 2) (theta φ 1) with h12 | h21 <;>
    rcases le_total (theta φ 2) (theta φ 0) with h02 | h20
  · exact ⟨φ, OM.NNN20.Reach.refl φ, h01, h12, rfl⟩
  · exact ⟨φ, OM.NNN20.Reach.refl φ, h01, h12, rfl⟩
  · obtain ⟨ψ, hreach, e⟩ := OM.NNN20.gen12 φ
    refine ⟨ψ, hreach, ?_, ?_, ?_⟩
    · rw [e, e]
      exact h02
    · rw [e, e]
      exact h21
    · simp only [e]
      simp
      ring
  · obtain ⟨ψ1, h1, e1⟩ := OM.NNN20.gen02 φ
    obtain ⟨ψ2, h2, e2⟩ := OM.NNN20.gen12 ψ1
    have e : ∀ j, theta ψ2 j = theta φ (![2, 0, 1] j) := by
      intro j
      rw [e2, e1]
      fin_cases j <;> rfl
    refine ⟨ψ2, h1.trans h2, ?_, ?_, ?_⟩
    · rw [e, e]
      exact h20
    · rw [e, e]
      exact h01
    · simp only [e]
      simp
      ring
  · obtain ⟨ψ, hreach, e⟩ := OM.NNN20.gen01 φ
    refine ⟨ψ, hreach, ?_, ?_, ?_⟩
    · rw [e, e]
      exact h10
    · rw [e, e]
      exact h02
    · simp only [e]
      simp
      ring
  · obtain ⟨ψ1, h1, e1⟩ := OM.NNN20.gen01 φ
    obtain ⟨ψ2, h2, e2⟩ := OM.NNN20.gen12 ψ1
    have e : ∀ j, theta ψ2 j = theta φ (![1, 2, 0] j) := by
      intro j
      rw [e2, e1]
      fin_cases j <;> rfl
    refine ⟨ψ2, h1.trans h2, ?_, ?_, ?_⟩
    · rw [e, e]
      exact h12
    · rw [e, e]
      exact h20
    · simp only [e]
      simp
      ring
  · exact ⟨φ, OM.NNN20.Reach.refl φ, by linarith, by linarith, rfl⟩
  · obtain ⟨ψ, hreach, e⟩ := OM.NNN20.gen02 φ
    refine ⟨ψ, hreach, ?_, ?_, ?_⟩
    · rw [e, e]
      exact h21
    · rw [e, e]
      exact h10
    · simp only [e]
      simp
      ring

lemma cubeBound_of_pair_tail {B : ℝ} (φ : PolMul.Spectral ℂ)
    (h : theta φ 1 + theta φ 2 ≤ B) : OM.NNN20.CubeBound B φ := by
  have hs : Fv φ (fun _ => 1) ≤ theta φ 1 + theta φ 2 := by
    simpa [starV, add_comm] using Fv_one_le_pair φ 0
  exact cubeBound_of_Fv φ (hs.trans h)

def UHyp (B : ℝ) : Prop :=
  ∀ φ : PolMul.Spectral ℂ, theta φ 1 ≤ theta φ 0 → theta φ 2 ≤ theta φ 1 →
    theta φ 0 + theta φ 1 + theta φ 2 ≤
      2 + 2 * Real.sqrt ((1 - theta φ 0) * (1 - theta φ 1) * (1 - theta φ 2)) →
    theta φ 0 - (theta φ 0 + theta φ 1 + theta φ 2) / 3 ≤ 3 / 2 - B →
    P2M.R88.Fv φ (fun _ => 1) ≤ B

lemma cubeBound_U (B : ℝ) (H : UHyp B) (φ : PolMul.Spectral ℂ) :
    OM.NNN20.CubeBound B φ := by
  obtain ⟨ψ, hreach, h10, h21, hsum⟩ := exists_sorted_theta φ
  apply hreach B
  have hsum_bound : theta ψ 0 + theta ψ 1 + theta ψ 2 ≤ 9 / 4 := by
    rw [hsum]
    exact OM.Omega.theta_sum_le_nine_quarters φ
  by_cases hr : theta ψ 0 - (theta ψ 0 + theta ψ 1 + theta ψ 2) / 3 ≤ 3 / 2 - B
  · have hF := H ψ h10 h21 (rectangular_region ψ) hr
    rw [Fv_eq] at hF
    exact cubeBound_of_Fv ψ hF
  · apply cubeBound_of_pair_tail
    push Not at hr
    linarith

def CHyp (B : ℝ) : Prop :=
  ∀ φ : PolMul.Spectral ℂ, theta φ 1 ≤ theta φ 0 → theta φ 2 ≤ theta φ 1 →
    theta φ 0 + theta φ 1 + theta φ 2 ≤ 2 →
    theta φ 0 - 2 / 3 ≤ 4 / 3 - B →
    P2M.R88.Fv φ (fun _ => 1) ≤ B

lemma cubeBound_C (B : ℝ) (H : CHyp B) (hω : OM.PolMul.omegaF ℂ = 2)
    (φ : PolMul.Spectral ℂ) : OM.NNN20.CubeBound B φ := by
  obtain ⟨ψ, hreach, h10, h21, hsum⟩ := exists_sorted_theta φ
  apply hreach B
  have hsum_bound : theta ψ 0 + theta ψ 1 + theta ψ 2 ≤ 2 := by
    rw [hsum]
    exact OM.NNN18.theta_sum_le_two hω φ
  by_cases hr : theta ψ 0 - 2 / 3 ≤ 4 / 3 - B
  · have hF := H ψ h10 h21 hsum_bound hr
    rw [Fv_eq] at hF
    exact cubeBound_of_Fv ψ hF
  · apply cubeBound_of_pair_tail
    push Not at hr
    linarith

theorem proof_R88_17 : S_R88_17 := by
  intro B hB H n T
  apply OM.NNN18.all_dims hB.le _ n T
  intro φ l S
  exact cubeBound_U B H φ l S

theorem proof_R88_18 : S_R88_18 := by
  intro B hB H hω n T
  apply OM.NNN18.all_dims hB.le _ n T
  intro φ l S
  exact cubeBound_C B H hω φ l S

end OM.NNN22
