import Lib.OM.NNN11.Averaged

/-! The finite 70-copy estimate from legal real rates and an affordable head. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN11
open CoordinateTensor OM.NNN.Raw
open ExtractionAB (X)
open Foundations.PairUnitExponents
set_option maxHeartbeats 2000000

def lengths (x y z : ℕ) : Fin 3 → ℕ := ![7 * min y z, 7 * min z x, 6 * min x y]
def degrees : Fin 3 → ℕ := ![70, 70, 42]
def rawAllowed (N d : ℕ) (a S t : ℝ) : ℝ := max 0 (d * (a - S) + N * codeK t)
def rawRates (x y z : ℕ) (t : Fin 3 → ℝ) (a : ℝ) (i : Fin 3) : ℝ :=
  rawAllowed (lengths x y z i) (degrees i) a (sourceLog x y z t i) (t i)

lemma rawAllowed_nonneg (N d : ℕ) (a S t : ℝ) : 0 ≤ rawAllowed N d a S t := le_max_left _ _

lemma rounded_raw_moment (N d : ℕ) (a S t : ℝ) :
    moment N (codeDimension 1 (rawAllowed N d a S t)) (d * S) (4 * t - 9 / 2) ≤
      (2 : ℝ) ^ ((d : ℝ) * a) := by
  have h := moment_rounded N (d * S) (4 * t - 9 / 2) (d * a)
  rw [raw_momentExponent] at h
  have he : (d : ℝ) * a - (d * S - N * codeK t) = d * (a - S) + N * codeK t := by ring
  rwa [he] at h

lemma rounded_head_any (L ρ t : Fin 3 → ℝ) (a : ℝ)
    (ht : ∀ i, 0 ≤ t i) (hs : ∑ i, t i = 9 / 4)
    (hh : ∑ i, t i * (L i - ρ i) ≤ 70 * a) :
    (∑ i, t i * (L i - (codeDimension 1 (ρ i) : ℝ) * Real.logb 2 7)) ≤
      70 * a + (9 / 4) * Real.logb 2 7 := by
  have hf (i) := mul_le_mul_of_nonneg_left (codeDimension_loss 1 (ρ i)) (ht i)
  simp only [Nat.cast_one, mul_one] at hf
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hf i)
  simp only [mul_add, add_mul, mul_one, Finset.sum_add_distrib, ← mul_assoc,
    ← Finset.sum_mul, hs] at hsum
  simp only [mul_sub, Finset.sum_sub_distrib, ← mul_assoc, ← Finset.sum_mul] at hh ⊢
  linarith

lemma rounded_head_price (L ρ t : Fin 3 → ℝ) (a : ℝ)
    (ht : ∀ i, 0 ≤ t i) (hs : ∑ i, t i = 9 / 4)
    (hh : ∑ i, t i * (L i - ρ i) ≤ 70 * a) :
    (2 : ℝ) ^ (∑ i, t i * (L i - (codeDimension 1 (ρ i) : ℝ) * Real.logb 2 7)) ≤
      (7 : ℝ) ^ (9 / 4 : ℝ) * (2 : ℝ) ^ (70 * a) := by
  apply (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    (rounded_head_any L ρ t a ht hs hh)).trans_eq
  have he : (2 : ℝ) ^ ((9 / 4 : ℝ) * Real.logb 2 7) = (7 : ℝ) ^ (9 / 4 : ℝ) := by
    rw [mul_comm, Real.rpow_mul (by norm_num), seven_rpow_logb]
  rw [Real.rpow_add (by norm_num), he, mul_comm]

theorem network70_rounded {x y z : ℕ} (φ : PolMul.Spectral ℂ)
    (t : Fin 3 → ℝ) (ht : ∀ i, theta φ i ≤ t i) (hs : ∑ i, t i = (9 : ℝ) / 4)
    (a : ℝ)
    (hcap : ∀ i, rawRates x y z t a i ≤ lengths x y z i * Real.logb 2 7)
    (hhead : ∑ i, t i * ((bondLog 21 21 28 x y z i : ℝ) - rawRates x y z t a i) ≤ 70 * a)
    (T : Tensor ℂ (X x) (X y) (X z)) : value φ T ≤ 2 * (2 : ℝ) ^ a := by
  let r : Fin 3 → ℕ := fun i => codeDimension 1 (rawRates x y z t a i)
  have hr (i : Fin 3) : r i ≤ lengths x y z i := by
    have h := codeDimension_le 1 (lengths x y z i) (hcap i)
    simpa only [Nat.mul_one] using! h
  have h := network70_raw_average φ t ht (by simpa only [Fin.sum_univ_three] using! hs) r
    (hr 0) (hr 1) (hr 2) T
  have hh := rounded_head_price (fun i => (bondLog 21 21 28 x y z i : ℝ))
    (rawRates x y z t a) t a (fun i => (theta_mem_Icc φ i).1.trans (ht i)) hs hhead
  have hc (i : Fin 3) := rounded_raw_moment (lengths x y z i) (degrees i) a (sourceLog x y z t i) (t i)
  have h0 := hc 0
  have h1 := hc 1
  have h2 := mul_le_mul_of_nonneg_right (hc 2) (show 0 ≤ value φ T ^ 28 from pow_nonneg (φ.nonneg _) _)
  change _ ≤ _ at hh
  dsimp only [r, rawRates] at h
  norm_num only [lengths, degrees, sourceLog, rawRates, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Nat.cast_ofNat] at h0 h1 h2 h hh
  apply network_scalar_exponent
  linarith only [h, hh, h0, h1, h2]

end OM.NNN11
