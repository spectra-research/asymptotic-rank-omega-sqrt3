import Lib.OM.NNN18.Contraction


noncomputable section
namespace OM.NNN18.FactsC

open FocusC (R R_pos)

variable {δ : Fin 3 → ℝ}

lemma tnn00 (hδ : InTri R δ) : (0 : ℝ) ≤ tariff C δ 0 0 := by
  have e : tariff C δ 0 0 = (3637 / 10000 : ℝ) + (-13 / 20 : ℝ) * δ 0 + (0 : ℝ) * δ 1 + (0 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, C] <;> ring
  rw [e]
  exact tri3_affine_ge R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma tle00 (hδ : InTri R δ) : tariff C δ 0 0 ≤ (1 : ℝ) := by
  have e : tariff C δ 0 0 = (3637 / 10000 : ℝ) + (-13 / 20 : ℝ) * δ 0 + (0 : ℝ) * δ 1 + (0 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, C] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma tnn01 (hδ : InTri R δ) : (0 : ℝ) ≤ tariff C δ 0 1 := by
  have e : tariff C δ 0 1 = (4431 / 10000 : ℝ) + (11 / 40 : ℝ) * δ 0 + (-3 / 8 : ℝ) * δ 1 + (3 / 8 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, C] <;> ring
  rw [e]
  exact tri3_affine_ge R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma tle01 (hδ : InTri R δ) : tariff C δ 0 1 ≤ (1 : ℝ) := by
  have e : tariff C δ 0 1 = (4431 / 10000 : ℝ) + (11 / 40 : ℝ) * δ 0 + (-3 / 8 : ℝ) * δ 1 + (3 / 8 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, C] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma tnn02 (hδ : InTri R δ) : (0 : ℝ) ≤ tariff C δ 0 2 := by
  have e : tariff C δ 0 2 = (4431 / 10000 : ℝ) + (11 / 40 : ℝ) * δ 0 + (3 / 8 : ℝ) * δ 1 + (-3 / 8 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, C] <;> ring
  rw [e]
  exact tri3_affine_ge R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma tle02 (hδ : InTri R δ) : tariff C δ 0 2 ≤ (1 : ℝ) := by
  have e : tariff C δ 0 2 = (4431 / 10000 : ℝ) + (11 / 40 : ℝ) * δ 0 + (3 / 8 : ℝ) * δ 1 + (-3 / 8 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, C] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma tnn10 (hδ : InTri R δ) : (0 : ℝ) ≤ tariff C δ 1 0 := by
  have e : tariff C δ 1 0 = (4431 / 10000 : ℝ) + (-3 / 8 : ℝ) * δ 0 + (11 / 40 : ℝ) * δ 1 + (3 / 8 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, C] <;> ring
  rw [e]
  exact tri3_affine_ge R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma tle10 (hδ : InTri R δ) : tariff C δ 1 0 ≤ (1 : ℝ) := by
  have e : tariff C δ 1 0 = (4431 / 10000 : ℝ) + (-3 / 8 : ℝ) * δ 0 + (11 / 40 : ℝ) * δ 1 + (3 / 8 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, C] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma tnn11 (hδ : InTri R δ) : (0 : ℝ) ≤ tariff C δ 1 1 := by
  have e : tariff C δ 1 1 = (3637 / 10000 : ℝ) + (0 : ℝ) * δ 0 + (-13 / 20 : ℝ) * δ 1 + (0 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, C] <;> ring
  rw [e]
  exact tri3_affine_ge R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma tle11 (hδ : InTri R δ) : tariff C δ 1 1 ≤ (1 : ℝ) := by
  have e : tariff C δ 1 1 = (3637 / 10000 : ℝ) + (0 : ℝ) * δ 0 + (-13 / 20 : ℝ) * δ 1 + (0 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, C] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma tnn12 (hδ : InTri R δ) : (0 : ℝ) ≤ tariff C δ 1 2 := by
  have e : tariff C δ 1 2 = (4431 / 10000 : ℝ) + (3 / 8 : ℝ) * δ 0 + (11 / 40 : ℝ) * δ 1 + (-3 / 8 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, C] <;> ring
  rw [e]
  exact tri3_affine_ge R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma tle12 (hδ : InTri R δ) : tariff C δ 1 2 ≤ (1 : ℝ) := by
  have e : tariff C δ 1 2 = (4431 / 10000 : ℝ) + (3 / 8 : ℝ) * δ 0 + (11 / 40 : ℝ) * δ 1 + (-3 / 8 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, C] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma tnn20 (hδ : InTri R δ) : (0 : ℝ) ≤ tariff C δ 2 0 := by
  have e : tariff C δ 2 0 = (4431 / 10000 : ℝ) + (-3 / 8 : ℝ) * δ 0 + (3 / 8 : ℝ) * δ 1 + (11 / 40 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, C] <;> ring
  rw [e]
  exact tri3_affine_ge R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma tle20 (hδ : InTri R δ) : tariff C δ 2 0 ≤ (1 : ℝ) := by
  have e : tariff C δ 2 0 = (4431 / 10000 : ℝ) + (-3 / 8 : ℝ) * δ 0 + (3 / 8 : ℝ) * δ 1 + (11 / 40 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, C] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma tnn21 (hδ : InTri R δ) : (0 : ℝ) ≤ tariff C δ 2 1 := by
  have e : tariff C δ 2 1 = (4431 / 10000 : ℝ) + (3 / 8 : ℝ) * δ 0 + (-3 / 8 : ℝ) * δ 1 + (11 / 40 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, C] <;> ring
  rw [e]
  exact tri3_affine_ge R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma tle21 (hδ : InTri R δ) : tariff C δ 2 1 ≤ (1 : ℝ) := by
  have e : tariff C δ 2 1 = (4431 / 10000 : ℝ) + (3 / 8 : ℝ) * δ 0 + (-3 / 8 : ℝ) * δ 1 + (11 / 40 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, C] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma tnn22 (hδ : InTri R δ) : (0 : ℝ) ≤ tariff C δ 2 2 := by
  have e : tariff C δ 2 2 = (3637 / 10000 : ℝ) + (0 : ℝ) * δ 0 + (0 : ℝ) * δ 1 + (-13 / 20 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, C] <;> ring
  rw [e]
  exact tri3_affine_ge R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma tle22 (hδ : InTri R δ) : tariff C δ 2 2 ≤ (1 : ℝ) := by
  have e : tariff C δ 2 2 = (3637 / 10000 : ℝ) + (0 : ℝ) * δ 0 + (0 : ℝ) * δ 1 + (-13 / 20 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, C] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma seed00 (hδ : InTri R δ) : star (theta C δ) 0 0 - tariff C δ 0 0 ≤ (1 / 2 : ℝ) := by
  have e : star (theta C δ) 0 0 - tariff C δ 0 0 = (-3637 / 10000 : ℝ) + (13 / 20 : ℝ) * δ 0 + (0 : ℝ) * δ 1 + (0 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, C] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma seed01 (hδ : InTri R δ) : star (theta C δ) 0 1 - tariff C δ 0 1 ≤ (1 / 2 : ℝ) := by
  have e : star (theta C δ) 0 1 - tariff C δ 0 1 = (6707 / 30000 : ℝ) + (-11 / 40 : ℝ) * δ 0 + (3 / 8 : ℝ) * δ 1 + (5 / 8 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, C] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma seed02 (hδ : InTri R δ) : star (theta C δ) 0 2 - tariff C δ 0 2 ≤ (1 / 2 : ℝ) := by
  have e : star (theta C δ) 0 2 - tariff C δ 0 2 = (6707 / 30000 : ℝ) + (-11 / 40 : ℝ) * δ 0 + (5 / 8 : ℝ) * δ 1 + (3 / 8 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, C] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma seed10 (hδ : InTri R δ) : star (theta C δ) 1 0 - tariff C δ 1 0 ≤ (1 / 2 : ℝ) := by
  have e : star (theta C δ) 1 0 - tariff C δ 1 0 = (6707 / 30000 : ℝ) + (3 / 8 : ℝ) * δ 0 + (-11 / 40 : ℝ) * δ 1 + (5 / 8 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, C] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma seed11 (hδ : InTri R δ) : star (theta C δ) 1 1 - tariff C δ 1 1 ≤ (1 / 2 : ℝ) := by
  have e : star (theta C δ) 1 1 - tariff C δ 1 1 = (-3637 / 10000 : ℝ) + (0 : ℝ) * δ 0 + (13 / 20 : ℝ) * δ 1 + (0 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, C] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma seed12 (hδ : InTri R δ) : star (theta C δ) 1 2 - tariff C δ 1 2 ≤ (1 / 2 : ℝ) := by
  have e : star (theta C δ) 1 2 - tariff C δ 1 2 = (6707 / 30000 : ℝ) + (5 / 8 : ℝ) * δ 0 + (-11 / 40 : ℝ) * δ 1 + (3 / 8 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, C] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma seed20 (hδ : InTri R δ) : star (theta C δ) 2 0 - tariff C δ 2 0 ≤ (1 / 2 : ℝ) := by
  have e : star (theta C δ) 2 0 - tariff C δ 2 0 = (6707 / 30000 : ℝ) + (3 / 8 : ℝ) * δ 0 + (5 / 8 : ℝ) * δ 1 + (-11 / 40 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, C] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma seed21 (hδ : InTri R δ) : star (theta C δ) 2 1 - tariff C δ 2 1 ≤ (1 / 2 : ℝ) := by
  have e : star (theta C δ) 2 1 - tariff C δ 2 1 = (6707 / 30000 : ℝ) + (5 / 8 : ℝ) * δ 0 + (3 / 8 : ℝ) * δ 1 + (-11 / 40 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, C] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma seed22 (hδ : InTri R δ) : star (theta C δ) 2 2 - tariff C δ 2 2 ≤ (1 / 2 : ℝ) := by
  have e : star (theta C δ) 2 2 - tariff C δ 2 2 = (-3637 / 10000 : ℝ) + (0 : ℝ) * δ 0 + (0 : ℝ) * δ 1 + (13 / 20 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, C] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma th0_0 (hδ : InTri R δ) : (0 : ℝ) ≤ theta C δ 0 := by
  have e : theta C δ 0 = (2 / 3 : ℝ) + (1 : ℝ) * δ 0 + (0 : ℝ) * δ 1 + (0 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, C] <;> ring
  rw [e]
  exact tri3_affine_ge R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma th1_0 (hδ : InTri R δ) : theta C δ 0 ≤ (1 : ℝ) := by
  have e : theta C δ 0 = (2 / 3 : ℝ) + (1 : ℝ) * δ 0 + (0 : ℝ) * δ 1 + (0 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, C] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma thq_0 (hδ : InTri R δ) : (1 / 4 : ℝ) ≤ theta C δ 0 := by
  have e : theta C δ 0 = (2 / 3 : ℝ) + (1 : ℝ) * δ 0 + (0 : ℝ) * δ 1 + (0 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, C] <;> ring
  rw [e]
  exact tri3_affine_ge R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma th0_1 (hδ : InTri R δ) : (0 : ℝ) ≤ theta C δ 1 := by
  have e : theta C δ 1 = (2 / 3 : ℝ) + (0 : ℝ) * δ 0 + (1 : ℝ) * δ 1 + (0 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, C] <;> ring
  rw [e]
  exact tri3_affine_ge R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma th1_1 (hδ : InTri R δ) : theta C δ 1 ≤ (1 : ℝ) := by
  have e : theta C δ 1 = (2 / 3 : ℝ) + (0 : ℝ) * δ 0 + (1 : ℝ) * δ 1 + (0 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, C] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma thq_1 (hδ : InTri R δ) : (1 / 4 : ℝ) ≤ theta C δ 1 := by
  have e : theta C δ 1 = (2 / 3 : ℝ) + (0 : ℝ) * δ 0 + (1 : ℝ) * δ 1 + (0 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, C] <;> ring
  rw [e]
  exact tri3_affine_ge R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma th0_2 (hδ : InTri R δ) : (0 : ℝ) ≤ theta C δ 2 := by
  have e : theta C δ 2 = (2 / 3 : ℝ) + (0 : ℝ) * δ 0 + (0 : ℝ) * δ 1 + (1 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, C] <;> ring
  rw [e]
  exact tri3_affine_ge R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma th1_2 (hδ : InTri R δ) : theta C δ 2 ≤ (1 : ℝ) := by
  have e : theta C δ 2 = (2 / 3 : ℝ) + (0 : ℝ) * δ 0 + (0 : ℝ) * δ 1 + (1 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, C] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma thq_2 (hδ : InTri R δ) : (1 / 4 : ℝ) ≤ theta C δ 2 := by
  have e : theta C δ 2 = (2 / 3 : ℝ) + (0 : ℝ) * δ 0 + (0 : ℝ) * δ 1 + (1 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, C] <;> ring
  rw [e]
  exact tri3_affine_ge R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma slh0 (hδ : InTri R δ) : theta C δ 0 - (theta C δ 1 + theta C δ 2) ≤ (0 : ℝ) := by
  have e : theta C δ 0 - (theta C δ 1 + theta C δ 2) = (-2 / 3 : ℝ) + (1 : ℝ) * δ 0 + (-1 : ℝ) * δ 1 + (-1 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, C] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma sli01 (hδ : InTri R δ) : theta C δ 1 - (2 * (4431 / 10000 : ℝ) + 2 * (11 / 40 : ℝ) * δ 1) ≤ (0 : ℝ) := by
  have e : theta C δ 1 - (2 * (4431 / 10000 : ℝ) + 2 * (11 / 40 : ℝ) * δ 1) = (-3293 / 15000 : ℝ) + (0 : ℝ) * δ 0 + (9 / 20 : ℝ) * δ 1 + (0 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, C] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma bt01 (hδ : InTri R δ) : (theta C δ 1 + (2 * (4431 / 10000 : ℝ) + 2 * (11 / 40 : ℝ) * δ 1)) / 2 ≤ (24 / 25 : ℝ) := by
  have e : (theta C δ 1 + (2 * (4431 / 10000 : ℝ) + 2 * (11 / 40 : ℝ) * δ 1)) / 2 = (23293 / 30000 : ℝ) + (0 : ℝ) * δ 0 + (31 / 40 : ℝ) * δ 1 + (0 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, C] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma sli02 (hδ : InTri R δ) : theta C δ 2 - (2 * (4431 / 10000 : ℝ) + 2 * (11 / 40 : ℝ) * δ 2) ≤ (0 : ℝ) := by
  have e : theta C δ 2 - (2 * (4431 / 10000 : ℝ) + 2 * (11 / 40 : ℝ) * δ 2) = (-3293 / 15000 : ℝ) + (0 : ℝ) * δ 0 + (0 : ℝ) * δ 1 + (9 / 20 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, C] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma bt02 (hδ : InTri R δ) : (theta C δ 2 + (2 * (4431 / 10000 : ℝ) + 2 * (11 / 40 : ℝ) * δ 2)) / 2 ≤ (24 / 25 : ℝ) := by
  have e : (theta C δ 2 + (2 * (4431 / 10000 : ℝ) + 2 * (11 / 40 : ℝ) * δ 2)) / 2 = (23293 / 30000 : ℝ) + (0 : ℝ) * δ 0 + (0 : ℝ) * δ 1 + (31 / 40 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, C] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma slh1 (hδ : InTri R δ) : theta C δ 1 - (theta C δ 0 + theta C δ 2) ≤ (0 : ℝ) := by
  have e : theta C δ 1 - (theta C δ 0 + theta C δ 2) = (-2 / 3 : ℝ) + (-1 : ℝ) * δ 0 + (1 : ℝ) * δ 1 + (-1 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, C] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma sli10 (hδ : InTri R δ) : theta C δ 0 - (2 * (4431 / 10000 : ℝ) + 2 * (11 / 40 : ℝ) * δ 0) ≤ (0 : ℝ) := by
  have e : theta C δ 0 - (2 * (4431 / 10000 : ℝ) + 2 * (11 / 40 : ℝ) * δ 0) = (-3293 / 15000 : ℝ) + (9 / 20 : ℝ) * δ 0 + (0 : ℝ) * δ 1 + (0 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, C] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma bt10 (hδ : InTri R δ) : (theta C δ 0 + (2 * (4431 / 10000 : ℝ) + 2 * (11 / 40 : ℝ) * δ 0)) / 2 ≤ (24 / 25 : ℝ) := by
  have e : (theta C δ 0 + (2 * (4431 / 10000 : ℝ) + 2 * (11 / 40 : ℝ) * δ 0)) / 2 = (23293 / 30000 : ℝ) + (31 / 40 : ℝ) * δ 0 + (0 : ℝ) * δ 1 + (0 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, C] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma sli12 (hδ : InTri R δ) : theta C δ 2 - (2 * (4431 / 10000 : ℝ) + 2 * (11 / 40 : ℝ) * δ 2) ≤ (0 : ℝ) := by
  have e : theta C δ 2 - (2 * (4431 / 10000 : ℝ) + 2 * (11 / 40 : ℝ) * δ 2) = (-3293 / 15000 : ℝ) + (0 : ℝ) * δ 0 + (0 : ℝ) * δ 1 + (9 / 20 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, C] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma bt12 (hδ : InTri R δ) : (theta C δ 2 + (2 * (4431 / 10000 : ℝ) + 2 * (11 / 40 : ℝ) * δ 2)) / 2 ≤ (24 / 25 : ℝ) := by
  have e : (theta C δ 2 + (2 * (4431 / 10000 : ℝ) + 2 * (11 / 40 : ℝ) * δ 2)) / 2 = (23293 / 30000 : ℝ) + (0 : ℝ) * δ 0 + (0 : ℝ) * δ 1 + (31 / 40 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, C] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma slh2 (hδ : InTri R δ) : theta C δ 2 - (theta C δ 0 + theta C δ 1) ≤ (0 : ℝ) := by
  have e : theta C δ 2 - (theta C δ 0 + theta C δ 1) = (-2 / 3 : ℝ) + (-1 : ℝ) * δ 0 + (-1 : ℝ) * δ 1 + (1 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, C] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma sli20 (hδ : InTri R δ) : theta C δ 0 - (2 * (4431 / 10000 : ℝ) + 2 * (11 / 40 : ℝ) * δ 0) ≤ (0 : ℝ) := by
  have e : theta C δ 0 - (2 * (4431 / 10000 : ℝ) + 2 * (11 / 40 : ℝ) * δ 0) = (-3293 / 15000 : ℝ) + (9 / 20 : ℝ) * δ 0 + (0 : ℝ) * δ 1 + (0 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, C] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma bt20 (hδ : InTri R δ) : (theta C δ 0 + (2 * (4431 / 10000 : ℝ) + 2 * (11 / 40 : ℝ) * δ 0)) / 2 ≤ (24 / 25 : ℝ) := by
  have e : (theta C δ 0 + (2 * (4431 / 10000 : ℝ) + 2 * (11 / 40 : ℝ) * δ 0)) / 2 = (23293 / 30000 : ℝ) + (31 / 40 : ℝ) * δ 0 + (0 : ℝ) * δ 1 + (0 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, C] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma sli21 (hδ : InTri R δ) : theta C δ 1 - (2 * (4431 / 10000 : ℝ) + 2 * (11 / 40 : ℝ) * δ 1) ≤ (0 : ℝ) := by
  have e : theta C δ 1 - (2 * (4431 / 10000 : ℝ) + 2 * (11 / 40 : ℝ) * δ 1) = (-3293 / 15000 : ℝ) + (0 : ℝ) * δ 0 + (9 / 20 : ℝ) * δ 1 + (0 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, C] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma bt21 (hδ : InTri R δ) : (theta C δ 1 + (2 * (4431 / 10000 : ℝ) + 2 * (11 / 40 : ℝ) * δ 1)) / 2 ≤ (24 / 25 : ℝ) := by
  have e : (theta C δ 1 + (2 * (4431 / 10000 : ℝ) + 2 * (11 / 40 : ℝ) * δ 1)) / 2 = (23293 / 30000 : ℝ) + (0 : ℝ) * δ 0 + (31 / 40 : ℝ) * δ 1 + (0 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, C] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])


lemma slope_all (hδ : InTri R δ) (h i : Fin 3) (e : ℝ) (he : 0 ≤ e) :
    NNN13.rawSlope (theta C δ) (parentsH C h e δ) i ≤ 0 := by
  fin_cases h <;> fin_cases i <;>
    simp [NNN13.rawSlope, NNN13.cross, parentsH, star, other, tariff] <;>
    first
    | (have := slh0 hδ; simp [theta, C] at this ⊢; linarith)
    | (have := slh1 hδ; simp [theta, C] at this ⊢; linarith)
    | (have := slh2 hδ; simp [theta, C] at this ⊢; linarith)
    | (have := sli01 hδ; simp [theta, C] at this ⊢; linarith)
    | (have := sli02 hδ; simp [theta, C] at this ⊢; linarith)
    | (have := sli10 hδ; simp [theta, C] at this ⊢; linarith)
    | (have := sli12 hδ; simp [theta, C] at this ⊢; linarith)
    | (have := sli20 hδ; simp [theta, C] at this ⊢; linarith)
    | (have := sli21 hδ; simp [theta, C] at this ⊢; linarith)

lemma beta_all (hδ : InTri R δ) (h i : Fin 3) (e : ℝ) (hi : i ≠ h) (he0 : 0 ≤ e)
    (he : e ≤ 1 / 25) : betaPackH C h e δ i ≤ 1 := by
  fin_cases h <;> fin_cases i <;> simp at hi <;>
    simp [betaPackH, parentsH, cross, tariff, other] <;>
    first
    | (have := bt01 hδ; simp [theta, C] at this ⊢; linarith)
    | (have := bt02 hδ; simp [theta, C] at this ⊢; linarith)
    | (have := bt10 hδ; simp [theta, C] at this ⊢; linarith)
    | (have := bt12 hδ; simp [theta, C] at this ⊢; linarith)
    | (have := bt20 hδ; simp [theta, C] at this ⊢; linarith)
    | (have := bt21 hδ; simp [theta, C] at this ⊢; linarith)

/-- The track facts of C. -/
def facts : TrackFacts C where
  R := R
  hR := R_pos
  tariff_nonneg := fun δ hδ => forall_fin3_2 (tnn00 hδ) (tnn01 hδ) (tnn02 hδ) (tnn10 hδ) (tnn11 hδ)
    (tnn12 hδ) (tnn20 hδ) (tnn21 hδ) (tnn22 hδ)
  tariff_le_one := fun δ hδ => forall_fin3_2 (tle00 hδ) (tle01 hδ) (tle02 hδ) (tle10 hδ) (tle11 hδ)
    (tle12 hδ) (tle20 hδ) (tle21 hδ) (tle22 hδ)
  seed := fun δ hδ => forall_fin3_2 (by linarith [seed00 hδ]) (by linarith [seed01 hδ])
    (by linarith [seed02 hδ]) (by linarith [seed10 hδ]) (by linarith [seed11 hδ])
    (by linarith [seed12 hδ]) (by linarith [seed20 hδ]) (by linarith [seed21 hδ])
    (by linarith [seed22 hδ])
  theta_mem := fun δ hδ => forall_fin3 ⟨th0_0 hδ, th1_0 hδ⟩ ⟨th0_1 hδ, th1_1 hδ⟩ ⟨th0_2 hδ, th1_2 hδ⟩
  theta_pos := fun δ hδ => forall_fin3 (by linarith [thq_0 hδ]) (by linarith [thq_1 hδ])
    (by linarith [thq_2 hδ])
  slope := fun δ hδ h i e he => slope_all hδ h i e he
  beta_le := fun δ hδ h i e hi he0 he => beta_all hδ h i e hi he0 he
  form_ord := fun δ hδ h x hx => (formH_C h hδ.1 hδ.2 hx).1
  form_pack := fun δ hδ h x hx => (formH_C h hδ.1 hδ.2 hx).2

end OM.NNN18.FactsC
