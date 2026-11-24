import Lib.OM.NNN12.Raw112
import Lib.OM.NNN12.RecursiveTransport
import Lib.OM.NNN11.Endpoints

/-! The raw helper at every physical heavy party and its two exact affine
pieces when C is the shortest residual coordinate. Off-sector pieces are
combined by their maximum; neither is assumed to be a global tensor bound. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN12
open CoordinateTensor OM.NNN.Raw Foundations.PairUnitExponents
open Foundations.OrientationTransport Lib.E.RectangularSpectrum
open NNN11 (bondLog)
set_option maxHeartbeats 2000000

def raw112PriceA (t : Fin 3 → ℝ) (v : Shape) : ℝ :=
  raw112Price ![t 2, t 1, t 0] (swap02Shape v)
def raw112PriceB (t : Fin 3 → ℝ) (v : Shape) : ℝ :=
  raw112Price ![t 0, t 2, t 1] (swap12Shape v)

theorem raw112_spectral_A (φ : PolMul.Spectral ℂ) (t : Fin 3 → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) 1) (hθ : ∀ i, theta φ i ≤ t i)
    (hs : t 0 + t 1 + t 2 = (9 : ℝ) / 4) (v : Shape) (T : DyadicTensor v) :
    value φ T ≤ (2 : ℝ) ^ raw112PriceA t v := by
  let ψ := pullPoint φ (rot 0)
  let t' : Fin 3 → ℝ := ![t 2, t 1, t 0]
  have ht' (i) : t' i ∈ Set.Icc (0 : ℝ) 1 := by
    fin_cases i <;> first | exact ht 2 | exact ht 1 | exact ht 0
  have hθ' (i) : theta ψ i ≤ t' i := by
    simp only [ψ, theta_legReindex]
    fin_cases i <;> first | exact hθ 2 | exact hθ 1 | exact hθ 0
  have hs' : t' 0 + t' 1 + t' 2 = (9 : ℝ) / 4 := by change t 2 + t 1 + t 0 = _; linarith
  have hh := raw112_spectral ψ t' ht' hθ' hs' (swap02Shape v) (swap02 T)
  rw [NNN11.value_swap02] at hh
  exact hh

theorem raw112_spectral_B (φ : PolMul.Spectral ℂ) (t : Fin 3 → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) 1) (hθ : ∀ i, theta φ i ≤ t i)
    (hs : t 0 + t 1 + t 2 = (9 : ℝ) / 4) (v : Shape) (T : DyadicTensor v) :
    value φ T ≤ (2 : ℝ) ^ raw112PriceB t v := by
  let ψ := pullPoint φ (rot 1)
  let t' : Fin 3 → ℝ := ![t 0, t 2, t 1]
  have ht' (i) : t' i ∈ Set.Icc (0 : ℝ) 1 := by
    fin_cases i <;> first | exact ht 0 | exact ht 2 | exact ht 1
  have hθ' (i) : theta ψ i ≤ t' i := by
    simp only [ψ, theta_legReindex]
    fin_cases i <;> first | exact hθ 0 | exact hθ 2 | exact hθ 1
  have hs' : t' 0 + t' 1 + t' 2 = (9 : ℝ) / 4 := by change t 0 + t 2 + t 1 = _; linarith
  have hh := raw112_spectral ψ t' ht' hθ' hs' (swap12Shape v) (swap12 T)
  rw [NNN11.value_swap12] at hh
  exact hh

def helper112Base (t : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![35 * t 2 + 42 * t 1 + 182 * t 1 * t 2,
    35 * t 2 + 42 * t 0 + 182 * t 0 * t 2,
    35 * t 1 + 35 * t 0 + 224 * t 0 * t 1 -
      7 * t 0 * rawCapacity 11 3 (t 0) - 7 * t 1 * rawCapacity 11 3 (t 1)]
def helper112Penalty (t : Fin 3 → ℝ) : ℝ := 10 * t 2 * NNN11.codeK (t 2)
def helper112Affine (j : Bool) (t : Fin 3 → ℝ) (x y z : ℝ) : ℝ :=
  (helper112Base t 0 * x + helper112Base t 1 * y + helper112Base t 2 * z -
    helper112Penalty t * (if j then y else x)) / raw112Denominator t

def helper112Coefficients (j : Bool) (t : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![(helper112Base t 0 - if j then 0 else helper112Penalty t) / raw112Denominator t,
    (helper112Base t 1 - if j then helper112Penalty t else 0) / raw112Denominator t,
    helper112Base t 2 / raw112Denominator t]

lemma helper112Affine_eq (j : Bool) (t : Fin 3 → ℝ) (x y z : ℝ) :
    helper112Affine j t x y z = helper112Coefficients j t 0 * x +
      helper112Coefficients j t 1 * y + helper112Coefficients j t 2 * z := by
  cases j <;> dsimp [helper112Affine, helper112Coefficients] <;> ring

lemma helper112Penalty_nonneg {t : Fin 3 → ℝ} (ht0 : 0 ≤ t 2) (ht1 : t 2 ≤ 1) :
    0 ≤ helper112Penalty t := by
  have hk : 0 ≤ NNN11.codeK (t 2) :=
    (by linarith [NNN11.codeK_one_bounds.1] : 0 ≤ NNN11.codeK 1).trans (NNN11.codeK_antitone ht1)
  unfold helper112Penalty
  positivity

lemma price_minimum_eq_max {D K : ℝ} (hD : 0 ≤ D) (hK : 0 ≤ K) (B x y : ℝ) :
    (B - K * min x y) / D = max ((B - K * x) / D) ((B - K * y) / D) := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, max_eq_left]
    exact div_le_div_of_nonneg_right (by nlinarith [mul_le_mul_of_nonneg_left h hK]) hD
  · rw [min_eq_right h, max_eq_right]
    exact div_le_div_of_nonneg_right (by nlinarith [mul_le_mul_of_nonneg_left h hK]) hD

lemma raw112Price_shortest_C (t : Fin 3 → ℝ) (v : Shape)
    (h0 : v 2 ≤ v 0) (h1 : v 2 ≤ v 1) :
    raw112Price t v = (helper112Base t 0 * v 0 + helper112Base t 1 * v 1 +
      helper112Base t 2 * v 2 - helper112Penalty t * min (v 0 : ℝ) (v 1 : ℝ)) / raw112Denominator t := by
  simp only [raw112Price, raw112Moments, raw112Lengths, starExponents, bondLog,
    Fin.sum_univ_three, raw112Degrees, raw112Alphabets, raw112Crossings,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    min_eq_left h0, min_eq_right h1, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat,
    Nat.cast_min, rawCapacity7, helper112Base, helper112Penalty]
  ring

lemma raw112Price_two_pieces (t : Fin 3 → ℝ) (v : Shape)
    (ht0 : 0 ≤ t 2) (ht1 : t 2 ≤ 1) (h0 : v 2 ≤ v 0) (h1 : v 2 ≤ v 1) :
    raw112Price t v = max (helper112Affine false t (v 0) (v 1) (v 2))
      (helper112Affine true t (v 0) (v 1) (v 2)) := by
  rw [raw112Price_shortest_C t v h0 h1]
  exact price_minimum_eq_max (raw112Denominator_pos ht1).le (helper112Penalty_nonneg ht0 ht1) _ _ _

theorem helper112_spectral_C (φ : PolMul.Spectral ℂ) (t : Fin 3 → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) 1) (hθ : ∀ i, theta φ i ≤ t i)
    (hs : t 0 + t 1 + t 2 = (9 : ℝ) / 4) (v : Shape)
    (h0 : v 2 ≤ v 0) (h1 : v 2 ≤ v 1) (T : DyadicTensor v) :
    value φ T ≤ (2 : ℝ) ^ max (helper112Affine false t (v 0) (v 1) (v 2))
      (helper112Affine true t (v 0) (v 1) (v 2)) := by
  rw [← raw112Price_two_pieces t v (ht 2).1 (ht 2).2 h0 h1]
  exact raw112_spectral φ t ht hθ hs v T

end OM.NNN12
