import Lib.OM.NNN12.Helper112
import Lib.OM.NNN12.Extraction

/-! The two complete helper branches on each full correction of the
28-copy network. The input has shape `(m,L,L)`, with `L ≤ m`.
Natural residual coordinates are checked before subtraction is cast. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN12
open CoordinateTensor OM.NNN.Raw NNN11.Network
open NNN11.ExtractionAB (X)
open Foundations.PairUnitExponents Codes
set_option maxHeartbeats 2000000

def swapShort (t : Fin 3 → ℝ) : Fin 3 → ℝ := ![t 0, t 2, t 1]
def inner28Intercept (j : Bool) (t : Fin 3 → ℝ) (m L : ℝ) : ℝ :=
  28 * helper112Affine j t m L L
def inner28Slope (j : Bool) (t : Fin 3 → ℝ) : ℝ :=
  t 1 - helper112Coefficients j t 0 - helper112Coefficients j t 2
def logMoment3 (D : ℝ) : ℝ :=
  Real.logb 2 (1 + 2 * (2 : ℝ) ^ D) - Real.logb 2 3
def inner28Moment (j : Bool) (t : Fin 3 → ℝ) (m L : ℝ) : ℝ :=
  inner28Intercept j t m L + 7 * L * logMoment3 (inner28Slope j t)
def inner28Full (t : Fin 3 → ℝ) (m L : ℝ) : ℝ :=
  max (inner28Moment false t m L) (inner28Moment true t m L)

lemma two_rpow_max_le (A B : ℝ) :
    (2 : ℝ) ^ max A B ≤ (2 : ℝ) ^ A + (2 : ℝ) ^ B := by
  rcases le_total A B with h | h
  · rw [max_eq_right h]; exact le_add_of_nonneg_left (by positivity)
  · rw [max_eq_left h]; exact le_add_of_nonneg_right (by positivity)

lemma helper112_residual_affine (j : Bool) (t : Fin 3 → ℝ) (m L E : ℝ) :
    helper112Affine j t (28 * m - E) (28 * L) (28 * L - E) + t 1 * E =
      inner28Intercept j t m L + inner28Slope j t * E := by
  simp only [inner28Intercept, inner28Slope, helper112Affine_eq]
  ring

lemma raw112_residual_CA_price {m L E : ℕ} (hL : L ≤ m) (hE : E ≤ 28 * L)
    (t : Fin 3 → ℝ) (ht0 : 0 ≤ t 2) (ht1 : t 2 ≤ 1) :
    raw112Price t ![28 * m - E, 28 * L, 28 * L - E] + t 1 * E =
      max (inner28Intercept false t m L + inner28Slope false t * E)
        (inner28Intercept true t m L + inner28Slope true t * E) := by
  have hEm : E ≤ 28 * m := hE.trans (Nat.mul_le_mul_left _ hL)
  rw [raw112Price_two_pieces t _ ht0 ht1
    (by dsimp; omega) (by dsimp; omega), ← max_add_add_right]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Nat.cast_sub hEm, Nat.cast_sub hE,
    Nat.cast_mul, Nat.cast_ofNat, helper112_residual_affine]

theorem inner28_CA_correction (φ : PolMul.Spectral ℂ) (t : Fin 3 → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) 1) (hθ : ∀ i, theta φ i ≤ t i)
    (hs : t 0 + t 1 + t 2 = (9 : ℝ) / 4) {m L : ℕ} (hL : L ≤ m)
    (T : Tensor ℂ (X m) (X L) (X L)) (w : Word 3 (7 * min L m))
    (P : Operator (BondAB (Fin 14) (Fin 7) (X m) (X L)))
    (Q : Operator (BondBC (Fin 7) (Fin 7) (X L) (X L))) :
    value φ (contract T P Q ((Layouts.heavy28 L m).kernel w)) ≤
      (2 : ℝ) ^ (inner28Intercept false t m L + inner28Slope false t * weight w) +
      (2 : ℝ) ^ (inner28Intercept true t m L + inner28Slope true t * weight w) := by
  have hE : weight w ≤ 28 * L := by have := weight_le w; have := Nat.min_le_left L m; omega
  have hh := (Layouts.heavy28 L m).full_CA_of_bound (B := Fin 7) w φ
    (raw112_spectral φ t ht hθ hs) (t 1) (hθ 1) T P Q
  norm_num only [Fintype.card_fin, Nat.reduceAdd, one_mul] at hh
  rw [raw112_residual_CA_price hL hE t (ht 2).1 (ht 2).2] at hh
  exact hh.trans (two_rpow_max_le _ _)

theorem inner28_AB_correction (φ : PolMul.Spectral ℂ) (t : Fin 3 → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) 1) (hθ : ∀ i, theta φ i ≤ t i)
    (hs : t 0 + t 1 + t 2 = (9 : ℝ) / 4) {m L : ℕ} (hL : L ≤ m)
    (T : Tensor ℂ (X m) (X L) (X L)) (w : Word 3 (7 * min m L))
    (Q : Operator (BondBC (Fin 7) (Fin 7) (X L) (X L)))
    (R : Operator (BondCA (Fin 7) (Fin 14) (X L) (X m))) :
    value φ (contract T ((Layouts.reverseHeavy28 m L).kernel w) Q R) ≤
      (2 : ℝ) ^ (inner28Intercept false (swapShort t) m L + inner28Slope false (swapShort t) * weight w) +
      (2 : ℝ) ^ (inner28Intercept true (swapShort t) m L + inner28Slope true (swapShort t) * weight w) := by
  have hE : weight w ≤ 28 * L := by have := weight_le w; have := Nat.min_le_right m L; omega
  have hh := (Layouts.reverseHeavy28 m L).full_AB_of_bound (C := Fin 7) w φ
    (raw112_spectral_B φ t ht hθ hs) (t 2) (hθ 2) T Q R
  norm_num only [Fintype.card_fin, Nat.reduceAdd, one_mul] at hh
  change value φ (contract T ((Layouts.reverseHeavy28 m L).kernel w) Q R) ≤
    (2 : ℝ) ^ (raw112Price (swapShort t) ![28 * m - weight w, 28 * L, 28 * L - weight w] +
      swapShort t 1 * weight w) at hh
  rw [raw112_residual_CA_price hL hE (swapShort t) (ht 1).1 (ht 1).2] at hh
  exact hh.trans (two_rpow_max_le _ _)

lemma inner28_moment_eq (j : Bool) (t : Fin 3 → ℝ) (m L : ℕ) :
    momentExponent 3 (7 * L) (inner28Intercept j t m L) (inner28Slope j t) =
      inner28Moment j t m L := by
  norm_num [momentExponent, inner28Moment, logMoment3]

end OM.NNN12
