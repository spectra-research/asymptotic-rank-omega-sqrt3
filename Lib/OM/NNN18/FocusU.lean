import Lib.OM.NNN18.Exact
import Lib.OM.NNN18.Triangle
import Lib.OM.NNN18.Moments
import Lib.OM.NNN18.OrdinaryU
import Lib.OM.NNN18.PackedUGates


noncomputable section
namespace OM.NNN18.FocusU

set_option maxHeartbeats 4000000

def R : ℝ := (10001 / 100000 : ℝ)
lemma R_pos : (0 : ℝ) < R := by norm_num [R]
lemma R_eq : ((U.R : ℚ) : ℝ) = R := by norm_num [U, R]
lemma R_eq' : ((10001 / 100000 : ℚ) : ℝ) = R := by norm_num [R]

variable {d y : ℝ}

lemma theta0_ge (hd₁ : -2 * R ≤ d) (hd₂ : d ≤ R) (hy₁ : -(d + 2 * R) ≤ y) (hy₂ : y ≤ d + 2 * R) :
    (1 / 5 : ℝ) ≤ theta U (delta d y) 0 := by
  have e : theta U (delta d y) 0 = (3 / 4 : ℝ) + (1 : ℝ) * d + (0 : ℝ) * y := by
    simp only [theta, delta, betaPack, parents0, cross, tariff_00, tariff_01, tariff_02, tariff_10, tariff_11, tariff_12, tariff_20, tariff_21, tariff_22, U, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue]
    push_cast; ring
  rw [e]
  exact tri_affine_ge R_pos hd₁ hd₂ hy₁ hy₂ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma theta0_nonneg (hd₁ : -2 * R ≤ d) (hd₂ : d ≤ R) (hy₁ : -(d + 2 * R) ≤ y) (hy₂ : y ≤ d + 2 * R) :
    (0 : ℝ) ≤ theta U (delta d y) 0 := by
  have e : theta U (delta d y) 0 = (3 / 4 : ℝ) + (1 : ℝ) * d + (0 : ℝ) * y := by
    simp only [theta, delta, betaPack, parents0, cross, tariff_00, tariff_01, tariff_02, tariff_10, tariff_11, tariff_12, tariff_20, tariff_21, tariff_22, U, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue]
    push_cast; ring
  rw [e]
  exact tri_affine_ge R_pos hd₁ hd₂ hy₁ hy₂ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma theta1_nonneg (hd₁ : -2 * R ≤ d) (hd₂ : d ≤ R) (hy₁ : -(d + 2 * R) ≤ y) (hy₂ : y ≤ d + 2 * R) :
    (0 : ℝ) ≤ theta U (delta d y) 1 := by
  have e : theta U (delta d y) 1 = (3 / 4 : ℝ) + (-1 / 2 : ℝ) * d + (1 / 2 : ℝ) * y := by
    simp only [theta, delta, betaPack, parents0, cross, tariff_00, tariff_01, tariff_02, tariff_10, tariff_11, tariff_12, tariff_20, tariff_21, tariff_22, U, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue]
    push_cast; ring
  rw [e]
  exact tri_affine_ge R_pos hd₁ hd₂ hy₁ hy₂ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma theta2_nonneg (hd₁ : -2 * R ≤ d) (hd₂ : d ≤ R) (hy₁ : -(d + 2 * R) ≤ y) (hy₂ : y ≤ d + 2 * R) :
    (0 : ℝ) ≤ theta U (delta d y) 2 := by
  have e : theta U (delta d y) 2 = (3 / 4 : ℝ) + (-1 / 2 : ℝ) * d + (-1 / 2 : ℝ) * y := by
    simp only [theta, delta, betaPack, parents0, cross, tariff_00, tariff_01, tariff_02, tariff_10, tariff_11, tariff_12, tariff_20, tariff_21, tariff_22, U, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue]
    push_cast; ring
  rw [e]
  exact tri_affine_ge R_pos hd₁ hd₂ hy₁ hy₂ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma theta1_le (hd₁ : -2 * R ≤ d) (hd₂ : d ≤ R) (hy₁ : -(d + 2 * R) ≤ y) (hy₂ : y ≤ d + 2 * R) :
    theta U (delta d y) 1 ≤ (43 / 50 : ℝ) := by
  have e : theta U (delta d y) 1 = (3 / 4 : ℝ) + (-1 / 2 : ℝ) * d + (1 / 2 : ℝ) * y := by
    simp only [theta, delta, betaPack, parents0, cross, tariff_00, tariff_01, tariff_02, tariff_10, tariff_11, tariff_12, tariff_20, tariff_21, tariff_22, U, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue]
    push_cast; ring
  rw [e]
  exact tri_affine_le R_pos hd₁ hd₂ hy₁ hy₂ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma theta2_le (hd₁ : -2 * R ≤ d) (hd₂ : d ≤ R) (hy₁ : -(d + 2 * R) ≤ y) (hy₂ : y ≤ d + 2 * R) :
    theta U (delta d y) 2 ≤ (43 / 50 : ℝ) := by
  have e : theta U (delta d y) 2 = (3 / 4 : ℝ) + (-1 / 2 : ℝ) * d + (-1 / 2 : ℝ) * y := by
    simp only [theta, delta, betaPack, parents0, cross, tariff_00, tariff_01, tariff_02, tariff_10, tariff_11, tariff_12, tariff_20, tariff_21, tariff_22, U, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue]
    push_cast; ring
  rw [e]
  exact tri_affine_le R_pos hd₁ hd₂ hy₁ hy₂ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma beta1_ge (hd₁ : -2 * R ≤ d) (hd₂ : d ≤ R) (hy₁ : -(d + 2 * R) ≤ y) (hy₂ : y ≤ d + 2 * R) :
    (16 / 25 : ℝ) ≤ betaPack U 0 (delta d y) 1 := by
  have e : betaPack U 0 (delta d y) 1 = (21841 / 25000 : ℝ) + (-2003 / 5000 : ℝ) * d + (2003 / 5000 : ℝ) * y := by
    simp only [theta, delta, betaPack, parents0, cross, tariff_00, tariff_01, tariff_02, tariff_10, tariff_11, tariff_12, tariff_20, tariff_21, tariff_22, U, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue]
    push_cast; ring
  rw [e]
  exact tri_affine_ge R_pos hd₁ hd₂ hy₁ hy₂ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma beta2_ge (hd₁ : -2 * R ≤ d) (hd₂ : d ≤ R) (hy₁ : -(d + 2 * R) ≤ y) (hy₂ : y ≤ d + 2 * R) :
    (16 / 25 : ℝ) ≤ betaPack U 0 (delta d y) 2 := by
  have e : betaPack U 0 (delta d y) 2 = (21841 / 25000 : ℝ) + (-2003 / 5000 : ℝ) * d + (-2003 / 5000 : ℝ) * y := by
    simp only [theta, delta, betaPack, parents0, cross, tariff_00, tariff_01, tariff_02, tariff_10, tariff_11, tariff_12, tariff_20, tariff_21, tariff_22, U, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue]
    push_cast; ring
  rw [e]
  exact tri_affine_ge R_pos hd₁ hd₂ hy₁ hy₂ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma A10_le (hd₁ : -2 * R ≤ d) (hd₂ : d ≤ R) (hy₁ : -(d + 2 * R) ≤ y) (hy₂ : y ≤ d + 2 * R) :
    tariff U (delta d y) 0 0 - tariff U (delta d y) 1 0 + (1 - 19 / 20) * betaPack U 0 (delta d y) 1 ≤ (4 / 25 : ℝ) := by
  have e : tariff U (delta d y) 0 0 - tariff U (delta d y) 1 0 + (1 - 19 / 20) * betaPack U 0 (delta d y) 1 = (-6531 / 125000 : ℝ) + (101 / 40000 : ℝ) * d + (2491 / 40000 : ℝ) * y := by
    simp only [theta, delta, betaPack, parents0, cross, tariff_00, tariff_01, tariff_02, tariff_10, tariff_11, tariff_12, tariff_20, tariff_21, tariff_22, U, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue]
    push_cast; ring
  rw [e]
  exact tri_affine_le R_pos hd₁ hd₂ hy₁ hy₂ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma A11_le (hd₁ : -2 * R ≤ d) (hd₂ : d ≤ R) (hy₁ : -(d + 2 * R) ≤ y) (hy₂ : y ≤ d + 2 * R) :
    tariff U (delta d y) 0 1 - tariff U (delta d y) 1 1 + (1 - 19 / 20) * betaPack U 0 (delta d y) 1 ≤ (4 / 25 : ℝ) := by
  have e : tariff U (delta d y) 0 1 - tariff U (delta d y) 1 1 + (1 - 19 / 20) * betaPack U 0 (delta d y) 1 = (34903 / 250000 : ℝ) + (-1803 / 25000 : ℝ) * d + (-1237 / 100000 : ℝ) * y := by
    simp only [theta, delta, betaPack, parents0, cross, tariff_00, tariff_01, tariff_02, tariff_10, tariff_11, tariff_12, tariff_20, tariff_21, tariff_22, U, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue]
    push_cast; ring
  rw [e]
  exact tri_affine_le R_pos hd₁ hd₂ hy₁ hy₂ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma A12_le (hd₁ : -2 * R ≤ d) (hd₂ : d ≤ R) (hy₁ : -(d + 2 * R) ≤ y) (hy₂ : y ≤ d + 2 * R) :
    tariff U (delta d y) 0 2 - tariff U (delta d y) 1 2 + (1 - 19 / 20) * betaPack U 0 (delta d y) 1 ≤ (4 / 25 : ℝ) := by
  have e : tariff U (delta d y) 0 2 - tariff U (delta d y) 1 2 + (1 - 19 / 20) * betaPack U 0 (delta d y) 1 = (21841 / 500000 : ℝ) + (-29353 / 200000 : ℝ) * d + (2491 / 40000 : ℝ) * y := by
    simp only [theta, delta, betaPack, parents0, cross, tariff_00, tariff_01, tariff_02, tariff_10, tariff_11, tariff_12, tariff_20, tariff_21, tariff_22, U, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue]
    push_cast; ring
  rw [e]
  exact tri_affine_le R_pos hd₁ hd₂ hy₁ hy₂ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma A20_le (hd₁ : -2 * R ≤ d) (hd₂ : d ≤ R) (hy₁ : -(d + 2 * R) ≤ y) (hy₂ : y ≤ d + 2 * R) :
    tariff U (delta d y) 0 0 - tariff U (delta d y) 2 0 + (1 - 19 / 20) * betaPack U 0 (delta d y) 2 ≤ (4 / 25 : ℝ) := by
  have e : tariff U (delta d y) 0 0 - tariff U (delta d y) 2 0 + (1 - 19 / 20) * betaPack U 0 (delta d y) 2 = (-6531 / 125000 : ℝ) + (101 / 40000 : ℝ) * d + (-2491 / 40000 : ℝ) * y := by
    simp only [theta, delta, betaPack, parents0, cross, tariff_00, tariff_01, tariff_02, tariff_10, tariff_11, tariff_12, tariff_20, tariff_21, tariff_22, U, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue]
    push_cast; ring
  rw [e]
  exact tri_affine_le R_pos hd₁ hd₂ hy₁ hy₂ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma A21_le (hd₁ : -2 * R ≤ d) (hd₂ : d ≤ R) (hy₁ : -(d + 2 * R) ≤ y) (hy₂ : y ≤ d + 2 * R) :
    tariff U (delta d y) 0 1 - tariff U (delta d y) 2 1 + (1 - 19 / 20) * betaPack U 0 (delta d y) 2 ≤ (4 / 25 : ℝ) := by
  have e : tariff U (delta d y) 0 1 - tariff U (delta d y) 2 1 + (1 - 19 / 20) * betaPack U 0 (delta d y) 2 = (21841 / 500000 : ℝ) + (-29353 / 200000 : ℝ) * d + (-2491 / 40000 : ℝ) * y := by
    simp only [theta, delta, betaPack, parents0, cross, tariff_00, tariff_01, tariff_02, tariff_10, tariff_11, tariff_12, tariff_20, tariff_21, tariff_22, U, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue]
    push_cast; ring
  rw [e]
  exact tri_affine_le R_pos hd₁ hd₂ hy₁ hy₂ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma A22_le (hd₁ : -2 * R ≤ d) (hd₂ : d ≤ R) (hy₁ : -(d + 2 * R) ≤ y) (hy₂ : y ≤ d + 2 * R) :
    tariff U (delta d y) 0 2 - tariff U (delta d y) 2 2 + (1 - 19 / 20) * betaPack U 0 (delta d y) 2 ≤ (4 / 25 : ℝ) := by
  have e : tariff U (delta d y) 0 2 - tariff U (delta d y) 2 2 + (1 - 19 / 20) * betaPack U 0 (delta d y) 2 = (34903 / 250000 : ℝ) + (-1803 / 25000 : ℝ) * d + (1237 / 100000 : ℝ) * y := by
    simp only [theta, delta, betaPack, parents0, cross, tariff_00, tariff_01, tariff_02, tariff_10, tariff_11, tariff_12, tariff_20, tariff_21, tariff_22, U, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue]
    push_cast; ring
  rw [e]
  exact tri_affine_le R_pos hd₁ hd₂ hy₁ hy₂ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma ordarg1_le (hd₁ : -2 * R ≤ d) (hd₂ : d ≤ R) (hy₁ : -(d + 2 * R) ≤ y) (hy₂ : y ≤ d + 2 * R) :
    theta U (delta d y) 1 - (tariff U (delta d y) 1 0 + tariff U (delta d y) 1 2) ≤ (7521 / 10000 : ℝ) := by
  have e : theta U (delta d y) 1 - (tariff U (delta d y) 1 0 + tariff U (delta d y) 1 2) = (-3091 / 12500 : ℝ) + (-497 / 2500 : ℝ) * d + (497 / 2500 : ℝ) * y := by
    simp only [theta, delta, betaPack, parents0, cross, tariff_00, tariff_01, tariff_02, tariff_10, tariff_11, tariff_12, tariff_20, tariff_21, tariff_22, U, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue]
    push_cast; ring
  rw [e]
  exact tri_affine_le R_pos hd₁ hd₂ hy₁ hy₂ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma ordarg1_ge (hd₁ : -2 * R ≤ d) (hd₂ : d ≤ R) (hy₁ : -(d + 2 * R) ≤ y) (hy₂ : y ≤ d + 2 * R) :
    (-12479 / 10000 : ℝ) ≤ theta U (delta d y) 1 - (tariff U (delta d y) 1 0 + tariff U (delta d y) 1 2) := by
  have e : theta U (delta d y) 1 - (tariff U (delta d y) 1 0 + tariff U (delta d y) 1 2) = (-3091 / 12500 : ℝ) + (-497 / 2500 : ℝ) * d + (497 / 2500 : ℝ) * y := by
    simp only [theta, delta, betaPack, parents0, cross, tariff_00, tariff_01, tariff_02, tariff_10, tariff_11, tariff_12, tariff_20, tariff_21, tariff_22, U, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue]
    push_cast; ring
  rw [e]
  exact tri_affine_ge R_pos hd₁ hd₂ hy₁ hy₂ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma packarg1_low (hd₁ : -2 * R ≤ d) (hd₂ : d ≤ R) (hy₁ : -(d + 2 * R) ≤ y) (hy₂ : y ≤ d + 2 * R) :
    (0 : ℝ) ≤ theta U (delta d y) 1 - (tariff U (delta d y) 1 0 + tariff U (delta d y) 1 2) + betaPack U 0 (delta d y) 1 / 2 := by
  have e : theta U (delta d y) 1 - (tariff U (delta d y) 1 0 + tariff U (delta d y) 1 2) + betaPack U 0 (delta d y) 1 / 2 = (9477 / 50000 : ℝ) + (-3991 / 10000 : ℝ) * d + (3991 / 10000 : ℝ) * y := by
    simp only [theta, delta, betaPack, parents0, cross, tariff_00, tariff_01, tariff_02, tariff_10, tariff_11, tariff_12, tariff_20, tariff_21, tariff_22, U, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue]
    push_cast; ring
  rw [e]
  exact tri_affine_ge R_pos hd₁ hd₂ hy₁ hy₂ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma packarg1_up (hd₁ : -2 * R ≤ d) (hd₂ : d ≤ R) (hy₁ : -(d + 2 * R) ≤ y) (hy₂ : y ≤ d + 2 * R) :
    theta U (delta d y) 1 - (tariff U (delta d y) 1 0 + tariff U (delta d y) 1 2) - ((-4958 / 17479 : ℝ) + 2) * betaPack U 0 (delta d y) 1 ≤ (0 : ℝ) := by
  have e : theta U (delta d y) 1 - (tariff U (delta d y) 1 0 + tariff U (delta d y) 1 2) - ((-4958 / 17479 : ℝ) + 2) * betaPack U 0 (delta d y) 1 = (-381642589 / 218487500 : ℝ) + (21357937 / 43697500 : ℝ) * d + (-21357937 / 43697500 : ℝ) * y := by
    simp only [theta, delta, betaPack, parents0, cross, tariff_00, tariff_01, tariff_02, tariff_10, tariff_11, tariff_12, tariff_20, tariff_21, tariff_22, U, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue]
    push_cast; ring
  rw [e]
  exact tri_affine_le R_pos hd₁ hd₂ hy₁ hy₂ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma packarg1_dn (hd₁ : -2 * R ≤ d) (hd₂ : d ≤ R) (hy₁ : -(d + 2 * R) ≤ y) (hy₂ : y ≤ d + 2 * R) :
    (0 : ℝ) ≤ theta U (delta d y) 1 - (tariff U (delta d y) 1 0 + tariff U (delta d y) 1 2) - ((-4958 / 17479 : ℝ) - 2) * betaPack U 0 (delta d y) 1 := by
  have e : theta U (delta d y) 1 - (tariff U (delta d y) 1 0 + tariff U (delta d y) 1 2) - ((-4958 / 17479 : ℝ) - 2) * betaPack U 0 (delta d y) 1 = (381875089 / 218487500 : ℝ) + (-48662937 / 43697500 : ℝ) * d + (48662937 / 43697500 : ℝ) * y := by
    simp only [theta, delta, betaPack, parents0, cross, tariff_00, tariff_01, tariff_02, tariff_10, tariff_11, tariff_12, tariff_20, tariff_21, tariff_22, U, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue]
    push_cast; ring
  rw [e]
  exact tri_affine_ge R_pos hd₁ hd₂ hy₁ hy₂ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma ordarg2_le (hd₁ : -2 * R ≤ d) (hd₂ : d ≤ R) (hy₁ : -(d + 2 * R) ≤ y) (hy₂ : y ≤ d + 2 * R) :
    theta U (delta d y) 2 - (tariff U (delta d y) 2 0 + tariff U (delta d y) 2 1) ≤ (7521 / 10000 : ℝ) := by
  have e : theta U (delta d y) 2 - (tariff U (delta d y) 2 0 + tariff U (delta d y) 2 1) = (-3091 / 12500 : ℝ) + (-497 / 2500 : ℝ) * d + (-497 / 2500 : ℝ) * y := by
    simp only [theta, delta, betaPack, parents0, cross, tariff_00, tariff_01, tariff_02, tariff_10, tariff_11, tariff_12, tariff_20, tariff_21, tariff_22, U, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue]
    push_cast; ring
  rw [e]
  exact tri_affine_le R_pos hd₁ hd₂ hy₁ hy₂ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma ordarg2_ge (hd₁ : -2 * R ≤ d) (hd₂ : d ≤ R) (hy₁ : -(d + 2 * R) ≤ y) (hy₂ : y ≤ d + 2 * R) :
    (-12479 / 10000 : ℝ) ≤ theta U (delta d y) 2 - (tariff U (delta d y) 2 0 + tariff U (delta d y) 2 1) := by
  have e : theta U (delta d y) 2 - (tariff U (delta d y) 2 0 + tariff U (delta d y) 2 1) = (-3091 / 12500 : ℝ) + (-497 / 2500 : ℝ) * d + (-497 / 2500 : ℝ) * y := by
    simp only [theta, delta, betaPack, parents0, cross, tariff_00, tariff_01, tariff_02, tariff_10, tariff_11, tariff_12, tariff_20, tariff_21, tariff_22, U, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue]
    push_cast; ring
  rw [e]
  exact tri_affine_ge R_pos hd₁ hd₂ hy₁ hy₂ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma packarg2_low (hd₁ : -2 * R ≤ d) (hd₂ : d ≤ R) (hy₁ : -(d + 2 * R) ≤ y) (hy₂ : y ≤ d + 2 * R) :
    (0 : ℝ) ≤ theta U (delta d y) 2 - (tariff U (delta d y) 2 0 + tariff U (delta d y) 2 1) + betaPack U 0 (delta d y) 2 / 2 := by
  have e : theta U (delta d y) 2 - (tariff U (delta d y) 2 0 + tariff U (delta d y) 2 1) + betaPack U 0 (delta d y) 2 / 2 = (9477 / 50000 : ℝ) + (-3991 / 10000 : ℝ) * d + (-3991 / 10000 : ℝ) * y := by
    simp only [theta, delta, betaPack, parents0, cross, tariff_00, tariff_01, tariff_02, tariff_10, tariff_11, tariff_12, tariff_20, tariff_21, tariff_22, U, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue]
    push_cast; ring
  rw [e]
  exact tri_affine_ge R_pos hd₁ hd₂ hy₁ hy₂ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma packarg2_up (hd₁ : -2 * R ≤ d) (hd₂ : d ≤ R) (hy₁ : -(d + 2 * R) ≤ y) (hy₂ : y ≤ d + 2 * R) :
    theta U (delta d y) 2 - (tariff U (delta d y) 2 0 + tariff U (delta d y) 2 1) - ((-4958 / 17479 : ℝ) + 2) * betaPack U 0 (delta d y) 2 ≤ (0 : ℝ) := by
  have e : theta U (delta d y) 2 - (tariff U (delta d y) 2 0 + tariff U (delta d y) 2 1) - ((-4958 / 17479 : ℝ) + 2) * betaPack U 0 (delta d y) 2 = (-381642589 / 218487500 : ℝ) + (21357937 / 43697500 : ℝ) * d + (21357937 / 43697500 : ℝ) * y := by
    simp only [theta, delta, betaPack, parents0, cross, tariff_00, tariff_01, tariff_02, tariff_10, tariff_11, tariff_12, tariff_20, tariff_21, tariff_22, U, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue]
    push_cast; ring
  rw [e]
  exact tri_affine_le R_pos hd₁ hd₂ hy₁ hy₂ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma packarg2_dn (hd₁ : -2 * R ≤ d) (hd₂ : d ≤ R) (hy₁ : -(d + 2 * R) ≤ y) (hy₂ : y ≤ d + 2 * R) :
    (0 : ℝ) ≤ theta U (delta d y) 2 - (tariff U (delta d y) 2 0 + tariff U (delta d y) 2 1) - ((-4958 / 17479 : ℝ) - 2) * betaPack U 0 (delta d y) 2 := by
  have e : theta U (delta d y) 2 - (tariff U (delta d y) 2 0 + tariff U (delta d y) 2 1) - ((-4958 / 17479 : ℝ) - 2) * betaPack U 0 (delta d y) 2 = (381875089 / 218487500 : ℝ) + (-48662937 / 43697500 : ℝ) * d + (-48662937 / 43697500 : ℝ) * y := by
    simp only [theta, delta, betaPack, parents0, cross, tariff_00, tariff_01, tariff_02, tariff_10, tariff_11, tariff_12, tariff_20, tariff_21, tariff_22, U, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue]
    push_cast; ring
  rw [e]
  exact tri_affine_ge R_pos hd₁ hd₂ hy₁ hy₂ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])


lemma args0_eq (e : ℝ) (β : Fin 3 → ℝ) (hβ : β 0 = 1) :
    args (theta U (delta d y)) β (parents0 U e (delta d y)) 0 = 2 * d - U.t := by
  simp only [args, hβ, div_one, parents0, cross, star_01, star_02, theta, delta,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  ring

lemma ordArgs_eq1 (e : ℝ) : args (theta U (delta d y)) betaOrd (parents0 U e (delta d y)) 1 =
    theta U (delta d y) 1 - (tariff U (delta d y) 1 0 + tariff U (delta d y) 1 2) - 2 * e := by
  simp only [args, betaOrd, div_one, parents0, cross, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

lemma ordArgs_eq2 (e : ℝ) : args (theta U (delta d y)) betaOrd (parents0 U e (delta d y)) 2 =
    theta U (delta d y) 2 - (tariff U (delta d y) 2 0 + tariff U (delta d y) 2 1) - 2 * e := by
  simp only [args, betaOrd, div_one, parents0, cross, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

/-- The retained moment bracket applies on the whole triangle (`|2d| ≤ 4R < 2`). -/
lemma ret_bracket (hd₁ : -2 * R ≤ d) (hd₂ : d ≤ R) :
    ell (2 * d - U.t) ≤ U.Lmaj 0 (2 * d - U.t) := by
  apply U_bracket0
  have : ((U.z0 0 : ℚ) : ℝ) = -U.t := by simp [Track.z0]
  rw [this, abs_le]
  constructor <;> norm_num [R] at hd₁ hd₂ ⊢ <;> linarith

theorem ordExact_nonneg {e : ℝ} (he₁ : 1 / 25 ≤ e) (he₂ : e ≤ 1 / 2) (hd₁ : -2 * R ≤ d)
    (hd₂ : d ≤ R) (hy₁ : -(d + 2 * R) ≤ y) (hy₂ : y ≤ d + 2 * R) {x : Fin 3 → ℝ}
    (hx : ∀ i, 0 ≤ x i) : 0 ≤ ordExact U e d y x := by
  have hR := R_pos
  have hhat := OrdU.ordHat_nonneg he₁ he₂ (d := d) (y := y)
    (by rw [R_eq]; linarith) (by rw [R_eq]; linarith) (by rw [R_eq]; linarith)
    (by rw [R_eq]; linarith) hx
  refine hhat.trans (form0_moment_mono ?_ hx ?_)
  · intro i; fin_cases i
    · exact theta0_nonneg hd₁ hd₂ hy₁ hy₂
    · exact theta1_nonneg hd₁ hd₂ hy₁ hy₂
    · exact theta2_nonneg hd₁ hd₂ hy₁ hy₂
  · intro i
    fin_cases i
    · show ell (args _ _ _ 0) ≤ _
      simp only [Matrix.cons_val_zero]
      rw [args0_eq e betaOrd rfl]
      exact ret_bracket hd₁ hd₂
    · show ell (args _ _ _ 1) ≤ U.Lmaj 1 (args _ _ _ 1)
      rw [ordArgs_eq1]
      apply U_bracket1
      have := ordarg1_le hd₁ hd₂ hy₁ hy₂
      have := ordarg1_ge hd₁ hd₂ hy₁ hy₂
      rw [abs_le]; constructor <;> norm_num [Track.z0, U] at * <;> linarith
    · show ell (args _ _ _ 2) ≤ U.Lmaj 1 (args _ _ _ 2)
      rw [ordArgs_eq2]
      apply U_bracket1
      have := ordarg2_le hd₁ hd₂ hy₁ hy₂
      have := ordarg2_ge hd₁ hd₂ hy₁ hy₂
      rw [abs_le]; constructor <;> norm_num [Track.z0, U] at * <;> linarith

/-- The packed moment argument at error 0 is in the packed bracket range. -/
lemma pack_bracket (i : Fin 3) (hi : i = 1 ∨ i = 2) (hd₁ : -2 * R ≤ d) (hd₂ : d ≤ R)
    (hy₁ : -(d + 2 * R) ≤ y) (hy₂ : y ≤ d + 2 * R) :
    ell (args (theta U (delta d y)) (betaPack U 0 (delta d y)) (parents0 U 0 (delta d y)) i)
      ≤ U.Lmaj 2 (args (theta U (delta d y)) (betaPack U 0 (delta d y))
          (parents0 U 0 (delta d y)) i) := by
  have hz0 : ((U.z0 2 : ℚ) : ℝ) = (-4958 / 17479 : ℝ) := by norm_num [Track.z0, U]
  rcases hi with rfl | rfl
  · have hb := beta1_ge hd₁ hd₂ hy₁ hy₂
    have hβ : (0 : ℝ) < betaPack U 0 (delta d y) 1 := by linarith
    have hargs : args (theta U (delta d y)) (betaPack U 0 (delta d y))
        (parents0 U 0 (delta d y)) 1 =
        (theta U (delta d y) 1 - (tariff U (delta d y) 1 0 + tariff U (delta d y) 1 2)) /
          betaPack U 0 (delta d y) 1 := by
      rw [args_pack_eq1, betaPack0_eq1]; ring
    rw [hargs]
    have l := packarg1_low hd₁ hd₂ hy₁ hy₂
    have u := packarg1_up hd₁ hd₂ hy₁ hy₂
    have w := packarg1_dn hd₁ hd₂ hy₁ hy₂
    apply U_bracket2
    · rw [hz0, abs_le]; constructor
      · rw [le_sub_iff_add_le, le_div_iff₀ hβ]; linarith
      · rw [sub_le_iff_le_add, div_le_iff₀ hβ]; linarith
    · rw [le_div_iff₀ hβ]; linarith
  · have hb := beta2_ge hd₁ hd₂ hy₁ hy₂
    have hβ : (0 : ℝ) < betaPack U 0 (delta d y) 2 := by linarith
    have hargs : args (theta U (delta d y)) (betaPack U 0 (delta d y))
        (parents0 U 0 (delta d y)) 2 =
        (theta U (delta d y) 2 - (tariff U (delta d y) 2 0 + tariff U (delta d y) 2 1)) /
          betaPack U 0 (delta d y) 2 := by
      rw [args_pack_eq2, betaPack0_eq2]; ring
    rw [hargs]
    have l := packarg2_low hd₁ hd₂ hy₁ hy₂
    have u := packarg2_up hd₁ hd₂ hy₁ hy₂
    have w := packarg2_dn hd₁ hd₂ hy₁ hy₂
    apply U_bracket2
    · rw [hz0, abs_le]; constructor
      · rw [le_sub_iff_add_le, le_div_iff₀ hβ]; linarith
      · rw [sub_le_iff_le_add, div_le_iff₀ hβ]; linarith
    · rw [le_div_iff₀ hβ]; linarith

theorem packExact_nonneg {e : ℝ} (he : 0 ≤ e) (hd₁ : -2 * R ≤ d) (hd₂ : d ≤ R)
    (hy₁ : -(d + 2 * R) ≤ y) (hy₂ : y ≤ d + 2 * R) {x : Fin 3 → ℝ} (hx : ∀ i, 0 ≤ x i) :
    0 ≤ packExact U e d y x := by
  have hR := R_pos
  have hθ : ∀ i, 0 ≤ theta U (delta d y) i := by
    intro i; fin_cases i
    · exact theta0_nonneg hd₁ hd₂ hy₁ hy₂
    · exact theta1_nonneg hd₁ hd₂ hy₁ hy₂
    · exact theta2_nonneg hd₁ hd₂ hy₁ hy₂
  have hhat := PackU.packHat_nonneg (d := d) (y := y)
    (by rw [R_eq']; linarith) (by rw [R_eq']; linarith) (by rw [R_eq']; linarith)
    (by rw [R_eq']; linarith) hx
  have h0 : packHat U 0 d y x ≤ packExact U 0 d y x := by
    apply form0_moment_mono hθ hx
    intro i; fin_cases i
    · show ell (args _ _ _ 0) ≤ _
      simp only [Matrix.cons_val_zero]
      rw [args0_eq 0 _ (by simp [betaPack])]
      exact ret_bracket hd₁ hd₂
    · exact pack_bracket 1 (Or.inl rfl) hd₁ hd₂ hy₁ hy₂
    · exact pack_bracket 2 (Or.inr rfl) hd₁ hd₂ hy₁ hy₂
  have hmono := packExact_mono U he hx hθ (by have h := theta0_ge hd₁ hd₂ hy₁ hy₂; norm_num at h ⊢; linarith)
    (by have h := theta1_le hd₁ hd₂ hy₁ hy₂; norm_num at h ⊢; linarith)
    (by have h := theta2_le hd₁ hd₂ hy₁ hy₂; norm_num at h ⊢; linarith)
    (by have h := beta1_ge hd₁ hd₂ hy₁ hy₂; norm_num at h ⊢; linarith)
    (by have h := beta2_ge hd₁ hd₂ hy₁ hy₂; norm_num at h ⊢; linarith)
    (forall_fin3 (by have h := A10_le hd₁ hd₂ hy₁ hy₂; norm_num at h ⊢; linarith)
      (by have h := A11_le hd₁ hd₂ hy₁ hy₂; norm_num at h ⊢; linarith)
      (by have h := A12_le hd₁ hd₂ hy₁ hy₂; norm_num at h ⊢; linarith))
    (forall_fin3 (by have h := A20_le hd₁ hd₂ hy₁ hy₂; norm_num at h ⊢; linarith)
      (by have h := A21_le hd₁ hd₂ hy₁ hy₂; norm_num at h ⊢; linarith)
      (by have h := A22_le hd₁ hd₂ hy₁ hy₂; norm_num at h ⊢; linarith))
  linarith

end OM.NNN18.FocusU
