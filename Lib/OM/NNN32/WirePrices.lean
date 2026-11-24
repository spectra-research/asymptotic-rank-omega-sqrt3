import Lib.OM.NNN32.MatchingWires
import Lib.OM.PolMul.SpectralFacts.Power
import Foundations.Tensors.Semicontinuity.SpectralPointExtension

/-! # The terminal prices of a four-party spectral point -/

noncomputable section

namespace OM.NNN32

open Semicontinuity AsymptoticSpectrumDuality

abbrev fourPreorder := tensorStrassenPreorder (F := ℂ) (k := 4) (by decide +kernel)

def wirePrice (φ : AsymptoticSpectrum fourPreorder) (i j : Fin 4) : ℝ :=
  if h : i ≠ j then Real.logb 2 (AsymptoticSpectrum.eval fourPreorder (wire 2 i j h) φ) else 0

lemma eval_wire (φ : AsymptoticSpectrum fourPreorder) (D : ℕ+) (i j : Fin 4) (hij : i ≠ j) :
    AsymptoticSpectrum.eval fourPreorder (wire D i j hij) φ = ((D:ℕ):ℝ)^wirePrice φ i j := by
  let f := ofAbstractSpectralPoint (K := ℂ) (k := 4) (by decide +kernel) φ
  let x := f.toFun (unitPairTensor (F := ℂ) 2 i j hij)
  have hx : 1 ≤ x := by
    have h := f.mono (unitPairTensor (F := ℂ) 1 i j hij) _
      (unitPairTensor_restricts_of_le (F := ℂ) i j hij (show ((1:ℕ+):ℕ) ≤ ((2:ℕ+):ℕ) by decide +kernel))
    simpa [x,f.unitPair_one] using h
  rw [wirePrice,dif_pos hij]
  change f.toFun (unitPairTensor (F := ℂ) D i j hij) = ((D:ℕ):ℝ)^Real.logb 2 x
  rw [OM.PolMul.SpectralFacts.unitPair_value_eq_rpow]
  change x^Real.logb 2 ((D:ℕ):ℝ) = _
  rw [Real.rpow_def_of_pos (zero_lt_one.trans_le hx),Real.rpow_def_of_pos (by positivity)]
  unfold Real.logb
  congr 1
  ring

lemma wirePrice_self (φ : AsymptoticSpectrum fourPreorder) (i : Fin 4) : wirePrice φ i i = 0 := by
  simp [wirePrice]

lemma wirePrice_nonneg (φ : AsymptoticSpectrum fourPreorder) (i j : Fin 4) : 0 ≤ wirePrice φ i j := by
  by_cases h : i=j
  · subst j; rw [wirePrice_self]
  let f := ofAbstractSpectralPoint (K := ℂ) (k := 4) (by decide +kernel) φ
  have h₁ := f.mono _ _ (unitPairTensor_restricts_of_le (F := ℂ) i j h
    (show ((1:ℕ+):ℕ) ≤ ((2:ℕ+):ℕ) by decide +kernel))
  rw [wirePrice,dif_pos h]
  apply Real.logb_nonneg (by norm_num)
  change 1 ≤ f.toFun _
  simpa [f.unitPair_one] using h₁

end OM.NNN32
