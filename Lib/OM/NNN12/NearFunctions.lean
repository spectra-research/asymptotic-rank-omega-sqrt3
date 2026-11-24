import Lib.OM.NNN12.Recursion
import Lib.OM.NNN12.Moments
import Lib.OM.NNN11.CodePrice

/-! The exact near-region head, retained moment, and supersolution functions.
These are the source formulas (39)--(43), with physical party A longest. -/
noncomputable section
open scoped BigOperators
namespace OM.NNN12
open NNN11 (bondLog)
set_option maxHeartbeats 1000000

def nearHead (t : Fin 3 → ℝ) (x y z : ℝ) : ℝ :=
  70 * (t 2 * y + t 1 * z) + 63 * (t 2 * x + t 0 * z) + 63 * (t 1 * x + t 0 * y)
def nearRetained (t : Fin 3 → ℝ) (y z : ℝ) : ℝ :=
  126 * (t 2 * y + t 1 * z) - 18 * z * NNN11.codeK (t 0)
def nearNumerator (t : Fin 3 → ℝ) (x y z : ℝ) : ℝ :=
  nearHead t x y z + t 1 * middleMoment (t 1) x y z +
    t 2 * shortMomentC (t 2) x y z + t 0 * nearRetained t y z

def nearPiA (t : Fin 3 → ℝ) (x y z : ℝ) : ℝ :=
  (nearHead t x y z + t 1 * middleMoment (t 1) x y z +
    t 2 * shortMomentA (t 2) x y z + t 0 * nearRetained t y z) / denominator (t 0)
def nearPiC (t : Fin 3 → ℝ) (x y z : ℝ) : ℝ :=
  nearNumerator t x y z / denominator (t 0)

def NearSupersolution (t : Fin 3 → ℝ) : Prop :=
  ∀ x y z : ℝ, y ≤ x → z ≤ y → 0 ≤ z → affine x y z ≤ upper * (y + z) →
    nearNumerator t x y z ≤ denominator (t 0) * affine x y z

lemma near_head_eq (t : Fin 3 → ℝ) (x y z : ℕ) :
    (∑ i, t i * (bondLog 70 63 63 x y z i : ℝ)) = nearHead t x y z := by
  simp only [Fin.sum_univ_three, bondLog, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  dsimp [nearHead]
  ring

lemma middle_moment_eq (t ε : ℝ) (x y z : ℕ) :
    momentExponent 19 (7 * z) (196 * (b * x + a * y + c * z) + 196 * ε * (x + y + z))
      (5 * (t - b - c)) = middleMoment t x y z + 196 * ε * (x + y + z) := by
  norm_num only [momentExponent, middleMoment, logMoment19, Nat.cast_mul, Nat.cast_ofNat]
  norm_num
  ring

lemma shortA_moment_eq (t ε : ℝ) (x y z : ℕ) :
    momentExponent 19 (7 * y) (196 * affine x y z + 196 * eta * (y - z) + 196 * ε * (x + y + z))
      (5 * (t - a - b - eta)) = shortMomentA t x y z + 196 * ε * (x + y + z) := by
  norm_num only [momentExponent, shortMomentA, logMoment19, Nat.cast_mul, Nat.cast_ofNat]
  norm_num
  ring

lemma shortC_moment_eq (t ε : ℝ) (x y z : ℕ) :
    momentExponent 19 (7 * y) (196 * (b * x + c * y + a * z) + 196 * ε * (x + y + z))
      (5 * (t - b - c)) = shortMomentC t x y z + 196 * ε * (x + y + z) := by
  norm_num only [momentExponent, shortMomentC, logMoment19, Nat.cast_mul, Nat.cast_ofNat]
  norm_num
  ring

lemma retained_moment_eq (t : Fin 3 → ℝ) (y z : ℕ) :
    momentExponent 7 (18 * z) (126 * (t 2 * y + t 1 * z)) (2 * (2 * t 0 - 9 / 4)) =
      nearRetained t y z := by
  have he : 2 * (2 * t 0 - 9 / 4) = 4 * t 0 - 9 / 2 := by ring
  norm_num only [momentExponent, nearRetained, NNN11.codeK, Nat.cast_mul, Nat.cast_ofNat, he]
  norm_num
  ring

lemma nearPiA_le_C {t : Fin 3 → ℝ} (ht0 : t 0 ≤ 1) (ht2 : 0 ≤ t 2)
    {x y z : ℝ} (hxy : y ≤ x) : nearPiA t x y z ≤ nearPiC t x y z := by
  apply div_le_div_of_nonneg_right _ (denominator_pos ht0).le
  dsimp [nearNumerator]
  linarith [mul_le_mul_of_nonneg_left (shortMomentA_le_C (t 2) (z := z) hxy) ht2]

end OM.NNN12
