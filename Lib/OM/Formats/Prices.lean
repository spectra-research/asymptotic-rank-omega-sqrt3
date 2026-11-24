import Lib.OM.NNN32.Implication
import Lib.OM.NNN36.PriceSpace

/-! # Supporting prices for three unequal dimensions -/

noncomputable section
namespace OM.Formats

open NNN22 NNN30.Net NNN.Raw Foundations.PairUnitExponents Foundations.HyperbolicLift Semicontinuity

/-- A supporting plane at the cube bounds the logarithmic spectral value of every tensor.
Powers remove the additive cost of rounding the three log-dimensions, including zero widths. -/
theorem log_eval_le_support (φ : PolMul.Spectral ℂ) (h : Fin 3 → ℝ)
    (hn : ∀ i, 0 ≤ h i)
    (hs : ∀ y : Fin 3 → ℝ, (∀ i, 0 ≤ y i) → Fv φ y ≤ ∑ i, h i * y i)
    {d : Fin 3 → ℕ+} (T : KTensor ℂ d) (hT : 0 < φ.eval T) :
    Real.logb 2 (φ.eval T) ≤ ∑ i, h i * Real.logb 2 (d i : ℕ) := by
  let w := fun i => Real.logb 2 (d i : ℕ)
  change Real.logb 2 (φ.eval T) ≤ ∑ i, h i * w i
  by_contra! hlt
  obtain ⟨n, hbig⟩ := exists_nat_gt ((∑ i, h i) / (Real.logb 2 (φ.eval T) - ∑ i, h i * w i))
  rw [div_lt_iff₀ (sub_pos.mpr hlt)] at hbig
  let Tn := PolMul.kronPow T n
  let I := fun i => Fin (((d i)^n : ℕ+) : ℕ)
  have hbound := cost_hub φ h hn hs I (fun a b c => Tn (idx3 a b c))
  rw [value_encode φ Tn, show φ.eval Tn = (φ.eval T)^n from NNN8.eval_kronPow φ T n] at hbound
  have hlog := (Real.logb_le_iff_le_rpow one_lt_two (pow_pos hT n)).2 hbound
  have hb (i) : bits (I i) = n * w i := by simp [bits, I, w, Real.logb_pow]
  simp only [Real.logb_pow, hb] at hlog
  rw [show (∑ i, h i * ((n : ℝ)*w i)) = n * ∑ i, h i * w i by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring] at hlog
  linarith only [hbig, hlog]

/-- Each pair tensor tests a sum of two supporting prices. Equality in the cube
perimeter bound forces equality in all three tests simultaneously. -/
theorem tight_support (hw : P2M.R113.finiteWitness) (φ : PolMul.Spectral ℂ) :
    ∃ h : Fin 3 → ℝ, (∀ i, 0 ≤ h i) ∧
      (∀ y : Fin 3 → ℝ, (∀ i, 0 ≤ y i) → Fv φ y ≤ ∑ i, h i * y i) ∧
      h 1 + h 2 = theta φ 0 ∧ h 0 + h 2 = theta φ 1 ∧ h 0 + h 1 = theta φ 2 := by
  obtain ⟨h, hn, hsum, hs⟩ := supporting_prices φ
  have pair (i : Fin 3) := (Fv_pair φ i).trans (hs _ (pairShape_nonneg i))
  have h₀ := pair 0
  have h₁ := pair 1
  have h₂ := pair 2
  simp [Fin.sum_univ_three, pairShape] at h₀ h₁ h₂
  have htotal := NNN32.proof_R113_11 hw φ
  rw [← hsum, Fin.sum_univ_three] at htotal
  exact ⟨h, hn, hs, by linarith, by linarith, by linarith⟩

end OM.Formats
