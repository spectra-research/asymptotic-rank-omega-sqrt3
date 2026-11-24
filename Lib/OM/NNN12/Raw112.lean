import Lib.OM.NNN12.Networks
import Lib.OM.NNN12.RawRates
import Lib.OM.NNN12.Stars

/-! The 112-copy helper on every rectangular format. All three attempted
rate overflows close by already-proved raw stars, before any code is used. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN12
open CoordinateTensor OM.NNN.Raw NNN11.Network
open NNN11 (bondLog)
open NNN11.ExtractionAB (X)
open Foundations.PairUnitExponents
set_option maxHeartbeats 2500000

def raw112Alphabets : Fin 3 → ℕ := ![11, 11, 7]
def raw112Crossings : Fin 3 → ℕ := ![3, 3, 2]
def raw112Degrees : Fin 3 → ℕ := ![112, 112, 70]
def raw112Lengths (v : Shape) : Fin 3 → ℕ :=
  ![7 * min (v 1) (v 2), 7 * min (v 2) (v 0), 10 * min (v 0) (v 1)]
def raw112Moments (t : Fin 3 → ℝ) (v : Shape) (i : Fin 3) : ℝ :=
  raw112Degrees i * starExponents (v 0) (v 1) (v 2) t i -
    raw112Lengths v i * rawCapacity (raw112Alphabets i) (raw112Crossings i) (t i)
def raw112Denominator (t : Fin 3 → ℝ) : ℝ := 364 - 42 * t 2
def raw112Price (t : Fin 3 → ℝ) (v : Shape) : ℝ :=
  ((∑ i, t i * (bondLog 35 35 42 (v 0) (v 1) (v 2) i : ℝ)) +
    (∑ i, t i * raw112Moments t v i)) / raw112Denominator t

def raw112Rates (t : Fin 3 → ℝ) (v : Shape) (A : ℝ) (i : Fin 3) : ℝ :=
  max 0 ((raw112Degrees i : ℝ) * A - raw112Moments t v i)

instance raw112Alphabets_prime (i : Fin 3) : Fact (raw112Alphabets i).Prime := by
  fin_cases i <;> dsimp [raw112Alphabets] <;> infer_instance

lemma raw112Denominator_pos {t : Fin 3 → ℝ} (ht : t 2 ≤ 1) : 0 < raw112Denominator t := by
  dsimp [raw112Denominator]
  linarith

lemma raw112_head (t : Fin 3 → ℝ) (v : Shape) (ht : ∀ i, 0 ≤ t i) (ht2 : t 2 ≤ 1)
    (hs : t 0 + t 1 + t 2 = (9 : ℝ) / 4) :
    (∑ i, t i * ((bondLog 35 35 42 (v 0) (v 1) (v 2) i : ℝ) -
      raw112Rates t v (raw112Price t v) i)) ≤ 112 * raw112Price t v := by
  apply balanced_clipped_head t _ _ _ 112 (raw112Price t v) ht
  have he : (112 : ℝ) + ∑ i, t i * (raw112Degrees i : ℝ) = raw112Denominator t := by
    rw [Fin.sum_univ_three]
    change 112 + (t 0 * 112 + t 1 * 112 + t 2 * 70) = 364 - 42 * t 2
    linarith
  rw [he, raw112Price]
  exact (mul_div_cancel₀ _ (raw112Denominator_pos ht2).ne').symm

lemma raw112_moment (t : Fin 3 → ℝ) (v : Shape) (A : ℝ) (i : Fin 3) :
    moment (raw112Alphabets i) (raw112Lengths v i)
      (codeDimension (raw112Alphabets i) (raw112Rates t v A i))
      (raw112Degrees i * starExponents (v 0) (v 1) (v 2) t i)
      (raw112Crossings i * (2 * t i - 9 / 4)) ≤ (2 : ℝ) ^ (raw112Degrees i * A) := by
  apply moment_rounded_of_le (M := raw112Moments t v i)
  exact (raw_moment_eq _ _ _ _ _ _).le

lemma raw112_overflow (φ : PolMul.Spectral ℂ) (t : Fin 3 → ℝ)
    (hθ : ∀ i, theta φ i ≤ t i) (v : Shape) (A : ℝ) (i : Fin 3)
    (ho : (raw112Lengths v i : ℝ) * Real.logb 2 (raw112Alphabets i) < raw112Rates t v A i)
    (T : DyadicTensor v) : value φ T ≤ (2 : ℝ) ^ A := by
  have hm : (0 : ℝ) < raw112Degrees i := by fin_cases i <;> norm_num [raw112Degrees]
  have hq := (alphabet_log_pos (q := raw112Alphabets i)).le
  have hcap := mul_le_mul_of_nonneg_left (rawCapacity_le (q := raw112Alphabets i)
    (raw112Crossings i) (t i)) (Nat.cast_nonneg (raw112Lengths v i) : (0 : ℝ) ≤ raw112Lengths v i)
  have hS := raw_rate_overflow hm (mul_nonneg (Nat.cast_nonneg _) hq) hcap ho
  have hv : value φ T ≤ (2 : ℝ) ^ (starExponents (v 0) (v 1) (v 2) t i) := by
    fin_cases i
    · exact value_le_star_A φ v T t hθ
    · exact value_le_star_B φ v T t hθ
    · exact value_le_star_C φ v T t hθ
  exact hv.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) hS.le)

theorem raw112_finite (φ : PolMul.Spectral ℂ) (t : Fin 3 → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) 1) (hθ : ∀ i, theta φ i ≤ t i)
    (hs : t 0 + t 1 + t 2 = (9 : ℝ) / 4) (v : Shape) (T : DyadicTensor v) :
    value φ T ≤ 2 * (2 : ℝ) ^ raw112Price t v := by
  by_cases hcap : ∀ i, raw112Rates t v (raw112Price t v) i ≤
      (raw112Lengths v i : ℝ) * Real.logb 2 (raw112Alphabets i)
  · let r : Fin 3 → ℕ := fun i => codeDimension (raw112Alphabets i) (raw112Rates t v (raw112Price t v) i)
    have hr (i : Fin 3) : r i ≤ raw112Lengths v i := codeDimension_le _ (hcap i)
    have hn := network112_raw_average (v 0) (v 1) (v 2) φ t hθ hs r hr T
    have hh := rounded_head_mixed raw112Alphabets
      (fun i => (bondLog 35 35 42 (v 0) (v 1) (v 2) i : ℝ)) t
      (raw112Rates t v (raw112Price t v)) ht (112 * raw112Price t v)
      (raw112_head t v (fun i => (ht i).1) (ht 2).2 hs)
    have h0 := raw112_moment t v (raw112Price t v) 0
    have h1 := raw112_moment t v (raw112Price t v) 1
    have h2 := mul_le_mul_of_nonneg_right (raw112_moment t v (raw112Price t v) 2)
      (show 0 ≤ value φ T ^ 42 from pow_nonneg (φ.nonneg _) 42)
    norm_num only [raw112Alphabets, raw112Degrees, raw112Lengths, raw112Crossings,
      starExponents, Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Nat.cast_ofNat,
      Nat.reduceAdd, Nat.reduceMul] at h0 h1 h2 hh
    apply retained_scalar_exponent (h := 42) (m := 70) (by norm_num) (by norm_num) constants112
    simp only [r, raw112Alphabets, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hn
    norm_num only [Nat.reduceAdd, Nat.cast_ofNat]
    nlinarith only [hn, hh, h0, h1, h2]
  · push_neg at hcap
    obtain ⟨i, hi⟩ := hcap
    have hh := raw112_overflow φ t hθ v (raw112Price t v) i hi T
    have hp : 0 ≤ (2 : ℝ) ^ raw112Price t v := by positivity
    linarith

lemma raw112Price_homogeneous (t : Fin 3 → ℝ) (q : ℕ) (v : Shape) :
    raw112Price t (powerShape q v) = q * raw112Price t v := by
  simp only [raw112Price, raw112Moments, raw112Lengths, starExponents, bondLog, powerShape,
    Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, raw112Degrees, min_mul_mul_left, Nat.cast_mul,
    Nat.cast_add, Nat.cast_ofNat]
  ring

/-- Constant-free raw helper, available for every natural dyadic format. -/
theorem raw112_spectral (φ : PolMul.Spectral ℂ) (t : Fin 3 → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) 1) (hθ : ∀ i, theta φ i ≤ t i)
    (hs : t 0 + t 1 + t 2 = (9 : ℝ) / 4) (v : Shape) (T : DyadicTensor v) :
    value φ T ≤ (2 : ℝ) ^ raw112Price t v :=
  remove_uniform_constant φ (raw112Price_homogeneous t) 2
    (raw112_finite φ t ht hθ hs) v T

end OM.NNN12
