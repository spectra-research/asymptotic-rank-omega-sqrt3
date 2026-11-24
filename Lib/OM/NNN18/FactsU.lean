import Lib.OM.NNN18.Contraction


noncomputable section
namespace OM.NNN18.FactsU

open FocusU (R R_pos)

variable {δ : Fin 3 → ℝ}

lemma tnn00 (hδ : InTri R δ) : (0 : ℝ) ≤ tariff U δ 0 0 := by
  have e : tariff U δ 0 0 = (40271 / 100000 : ℝ) + (-35329 / 50000 : ℝ) * δ 0 + (0 : ℝ) * δ 1 + (0 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, U] <;> ring
  rw [e]
  exact tri3_affine_ge R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma tle00 (hδ : InTri R δ) : tariff U δ 0 0 ≤ (1 : ℝ) := by
  have e : tariff U δ 0 0 = (40271 / 100000 : ℝ) + (-35329 / 50000 : ℝ) * δ 0 + (0 : ℝ) * δ 1 + (0 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, U] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma tnn01 (hδ : InTri R δ) : (0 : ℝ) ≤ tariff U δ 0 1 := by
  have e : tariff U δ 0 1 = (6233 / 12500 : ℝ) + (753 / 2500 : ℝ) * δ 0 + (-38569 / 100000 : ℝ) * δ 1 + (38569 / 100000 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, U] <;> ring
  rw [e]
  exact tri3_affine_ge R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma tle01 (hδ : InTri R δ) : tariff U δ 0 1 ≤ (1 : ℝ) := by
  have e : tariff U δ 0 1 = (6233 / 12500 : ℝ) + (753 / 2500 : ℝ) * δ 0 + (-38569 / 100000 : ℝ) * δ 1 + (38569 / 100000 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, U] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma tnn02 (hδ : InTri R δ) : (0 : ℝ) ≤ tariff U δ 0 2 := by
  have e : tariff U δ 0 2 = (6233 / 12500 : ℝ) + (753 / 2500 : ℝ) * δ 0 + (38569 / 100000 : ℝ) * δ 1 + (-38569 / 100000 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, U] <;> ring
  rw [e]
  exact tri3_affine_ge R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma tle02 (hδ : InTri R δ) : tariff U δ 0 2 ≤ (1 : ℝ) := by
  have e : tariff U δ 0 2 = (6233 / 12500 : ℝ) + (753 / 2500 : ℝ) * δ 0 + (38569 / 100000 : ℝ) * δ 1 + (-38569 / 100000 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, U] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma tnn10 (hδ : InTri R δ) : (0 : ℝ) ≤ tariff U δ 1 0 := by
  have e : tariff U δ 1 0 = (6233 / 12500 : ℝ) + (-38569 / 100000 : ℝ) * δ 0 + (753 / 2500 : ℝ) * δ 1 + (38569 / 100000 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, U] <;> ring
  rw [e]
  exact tri3_affine_ge R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma tle10 (hδ : InTri R δ) : tariff U δ 1 0 ≤ (1 : ℝ) := by
  have e : tariff U δ 1 0 = (6233 / 12500 : ℝ) + (-38569 / 100000 : ℝ) * δ 0 + (753 / 2500 : ℝ) * δ 1 + (38569 / 100000 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, U] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma tnn11 (hδ : InTri R δ) : (0 : ℝ) ≤ tariff U δ 1 1 := by
  have e : tariff U δ 1 1 = (40271 / 100000 : ℝ) + (0 : ℝ) * δ 0 + (-35329 / 50000 : ℝ) * δ 1 + (0 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, U] <;> ring
  rw [e]
  exact tri3_affine_ge R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma tle11 (hδ : InTri R δ) : tariff U δ 1 1 ≤ (1 : ℝ) := by
  have e : tariff U δ 1 1 = (40271 / 100000 : ℝ) + (0 : ℝ) * δ 0 + (-35329 / 50000 : ℝ) * δ 1 + (0 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, U] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma tnn12 (hδ : InTri R δ) : (0 : ℝ) ≤ tariff U δ 1 2 := by
  have e : tariff U δ 1 2 = (6233 / 12500 : ℝ) + (38569 / 100000 : ℝ) * δ 0 + (753 / 2500 : ℝ) * δ 1 + (-38569 / 100000 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, U] <;> ring
  rw [e]
  exact tri3_affine_ge R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma tle12 (hδ : InTri R δ) : tariff U δ 1 2 ≤ (1 : ℝ) := by
  have e : tariff U δ 1 2 = (6233 / 12500 : ℝ) + (38569 / 100000 : ℝ) * δ 0 + (753 / 2500 : ℝ) * δ 1 + (-38569 / 100000 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, U] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma tnn20 (hδ : InTri R δ) : (0 : ℝ) ≤ tariff U δ 2 0 := by
  have e : tariff U δ 2 0 = (6233 / 12500 : ℝ) + (-38569 / 100000 : ℝ) * δ 0 + (38569 / 100000 : ℝ) * δ 1 + (753 / 2500 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, U] <;> ring
  rw [e]
  exact tri3_affine_ge R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma tle20 (hδ : InTri R δ) : tariff U δ 2 0 ≤ (1 : ℝ) := by
  have e : tariff U δ 2 0 = (6233 / 12500 : ℝ) + (-38569 / 100000 : ℝ) * δ 0 + (38569 / 100000 : ℝ) * δ 1 + (753 / 2500 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, U] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma tnn21 (hδ : InTri R δ) : (0 : ℝ) ≤ tariff U δ 2 1 := by
  have e : tariff U δ 2 1 = (6233 / 12500 : ℝ) + (38569 / 100000 : ℝ) * δ 0 + (-38569 / 100000 : ℝ) * δ 1 + (753 / 2500 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, U] <;> ring
  rw [e]
  exact tri3_affine_ge R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma tle21 (hδ : InTri R δ) : tariff U δ 2 1 ≤ (1 : ℝ) := by
  have e : tariff U δ 2 1 = (6233 / 12500 : ℝ) + (38569 / 100000 : ℝ) * δ 0 + (-38569 / 100000 : ℝ) * δ 1 + (753 / 2500 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, U] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma tnn22 (hδ : InTri R δ) : (0 : ℝ) ≤ tariff U δ 2 2 := by
  have e : tariff U δ 2 2 = (40271 / 100000 : ℝ) + (0 : ℝ) * δ 0 + (0 : ℝ) * δ 1 + (-35329 / 50000 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, U] <;> ring
  rw [e]
  exact tri3_affine_ge R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma tle22 (hδ : InTri R δ) : tariff U δ 2 2 ≤ (1 : ℝ) := by
  have e : tariff U δ 2 2 = (40271 / 100000 : ℝ) + (0 : ℝ) * δ 0 + (0 : ℝ) * δ 1 + (-35329 / 50000 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, U] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma seed00 (hδ : InTri R δ) : star (theta U δ) 0 0 - tariff U δ 0 0 ≤ (1 / 2 : ℝ) := by
  have e : star (theta U δ) 0 0 - tariff U δ 0 0 = (-40271 / 100000 : ℝ) + (35329 / 50000 : ℝ) * δ 0 + (0 : ℝ) * δ 1 + (0 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, U] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma seed01 (hδ : InTri R δ) : star (theta U δ) 0 1 - tariff U δ 0 1 ≤ (1 / 2 : ℝ) := by
  have e : star (theta U δ) 0 1 - tariff U δ 0 1 = (1571 / 6250 : ℝ) + (-753 / 2500 : ℝ) * δ 0 + (38569 / 100000 : ℝ) * δ 1 + (61431 / 100000 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, U] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma seed02 (hδ : InTri R δ) : star (theta U δ) 0 2 - tariff U δ 0 2 ≤ (1 / 2 : ℝ) := by
  have e : star (theta U δ) 0 2 - tariff U δ 0 2 = (1571 / 6250 : ℝ) + (-753 / 2500 : ℝ) * δ 0 + (61431 / 100000 : ℝ) * δ 1 + (38569 / 100000 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, U] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma seed10 (hδ : InTri R δ) : star (theta U δ) 1 0 - tariff U δ 1 0 ≤ (1 / 2 : ℝ) := by
  have e : star (theta U δ) 1 0 - tariff U δ 1 0 = (1571 / 6250 : ℝ) + (38569 / 100000 : ℝ) * δ 0 + (-753 / 2500 : ℝ) * δ 1 + (61431 / 100000 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, U] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma seed11 (hδ : InTri R δ) : star (theta U δ) 1 1 - tariff U δ 1 1 ≤ (1 / 2 : ℝ) := by
  have e : star (theta U δ) 1 1 - tariff U δ 1 1 = (-40271 / 100000 : ℝ) + (0 : ℝ) * δ 0 + (35329 / 50000 : ℝ) * δ 1 + (0 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, U] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma seed12 (hδ : InTri R δ) : star (theta U δ) 1 2 - tariff U δ 1 2 ≤ (1 / 2 : ℝ) := by
  have e : star (theta U δ) 1 2 - tariff U δ 1 2 = (1571 / 6250 : ℝ) + (61431 / 100000 : ℝ) * δ 0 + (-753 / 2500 : ℝ) * δ 1 + (38569 / 100000 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, U] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma seed20 (hδ : InTri R δ) : star (theta U δ) 2 0 - tariff U δ 2 0 ≤ (1 / 2 : ℝ) := by
  have e : star (theta U δ) 2 0 - tariff U δ 2 0 = (1571 / 6250 : ℝ) + (38569 / 100000 : ℝ) * δ 0 + (61431 / 100000 : ℝ) * δ 1 + (-753 / 2500 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, U] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma seed21 (hδ : InTri R δ) : star (theta U δ) 2 1 - tariff U δ 2 1 ≤ (1 / 2 : ℝ) := by
  have e : star (theta U δ) 2 1 - tariff U δ 2 1 = (1571 / 6250 : ℝ) + (61431 / 100000 : ℝ) * δ 0 + (38569 / 100000 : ℝ) * δ 1 + (-753 / 2500 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, U] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma seed22 (hδ : InTri R δ) : star (theta U δ) 2 2 - tariff U δ 2 2 ≤ (1 / 2 : ℝ) := by
  have e : star (theta U δ) 2 2 - tariff U δ 2 2 = (-40271 / 100000 : ℝ) + (0 : ℝ) * δ 0 + (0 : ℝ) * δ 1 + (35329 / 50000 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, U] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma th0_0 (hδ : InTri R δ) : (0 : ℝ) ≤ theta U δ 0 := by
  have e : theta U δ 0 = (3 / 4 : ℝ) + (1 : ℝ) * δ 0 + (0 : ℝ) * δ 1 + (0 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, U] <;> ring
  rw [e]
  exact tri3_affine_ge R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma th1_0 (hδ : InTri R δ) : theta U δ 0 ≤ (1 : ℝ) := by
  have e : theta U δ 0 = (3 / 4 : ℝ) + (1 : ℝ) * δ 0 + (0 : ℝ) * δ 1 + (0 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, U] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma thq_0 (hδ : InTri R δ) : (1 / 4 : ℝ) ≤ theta U δ 0 := by
  have e : theta U δ 0 = (3 / 4 : ℝ) + (1 : ℝ) * δ 0 + (0 : ℝ) * δ 1 + (0 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, U] <;> ring
  rw [e]
  exact tri3_affine_ge R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma th0_1 (hδ : InTri R δ) : (0 : ℝ) ≤ theta U δ 1 := by
  have e : theta U δ 1 = (3 / 4 : ℝ) + (0 : ℝ) * δ 0 + (1 : ℝ) * δ 1 + (0 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, U] <;> ring
  rw [e]
  exact tri3_affine_ge R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma th1_1 (hδ : InTri R δ) : theta U δ 1 ≤ (1 : ℝ) := by
  have e : theta U δ 1 = (3 / 4 : ℝ) + (0 : ℝ) * δ 0 + (1 : ℝ) * δ 1 + (0 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, U] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma thq_1 (hδ : InTri R δ) : (1 / 4 : ℝ) ≤ theta U δ 1 := by
  have e : theta U δ 1 = (3 / 4 : ℝ) + (0 : ℝ) * δ 0 + (1 : ℝ) * δ 1 + (0 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, U] <;> ring
  rw [e]
  exact tri3_affine_ge R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma th0_2 (hδ : InTri R δ) : (0 : ℝ) ≤ theta U δ 2 := by
  have e : theta U δ 2 = (3 / 4 : ℝ) + (0 : ℝ) * δ 0 + (0 : ℝ) * δ 1 + (1 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, U] <;> ring
  rw [e]
  exact tri3_affine_ge R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma th1_2 (hδ : InTri R δ) : theta U δ 2 ≤ (1 : ℝ) := by
  have e : theta U δ 2 = (3 / 4 : ℝ) + (0 : ℝ) * δ 0 + (0 : ℝ) * δ 1 + (1 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, U] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma thq_2 (hδ : InTri R δ) : (1 / 4 : ℝ) ≤ theta U δ 2 := by
  have e : theta U δ 2 = (3 / 4 : ℝ) + (0 : ℝ) * δ 0 + (0 : ℝ) * δ 1 + (1 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, U] <;> ring
  rw [e]
  exact tri3_affine_ge R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma slh0 (hδ : InTri R δ) : theta U δ 0 - (theta U δ 1 + theta U δ 2) ≤ (0 : ℝ) := by
  have e : theta U δ 0 - (theta U δ 1 + theta U δ 2) = (-3 / 4 : ℝ) + (1 : ℝ) * δ 0 + (-1 : ℝ) * δ 1 + (-1 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, U] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma sli01 (hδ : InTri R δ) : theta U δ 1 - (2 * (6233 / 12500 : ℝ) + 2 * (753 / 2500 : ℝ) * δ 1) ≤ (0 : ℝ) := by
  have e : theta U δ 1 - (2 * (6233 / 12500 : ℝ) + 2 * (753 / 2500 : ℝ) * δ 1) = (-3091 / 12500 : ℝ) + (0 : ℝ) * δ 0 + (497 / 1250 : ℝ) * δ 1 + (0 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, U] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma bt01 (hδ : InTri R δ) : (theta U δ 1 + (2 * (6233 / 12500 : ℝ) + 2 * (753 / 2500 : ℝ) * δ 1)) / 2 ≤ (24 / 25 : ℝ) := by
  have e : (theta U δ 1 + (2 * (6233 / 12500 : ℝ) + 2 * (753 / 2500 : ℝ) * δ 1)) / 2 = (21841 / 25000 : ℝ) + (0 : ℝ) * δ 0 + (2003 / 2500 : ℝ) * δ 1 + (0 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, U] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma sli02 (hδ : InTri R δ) : theta U δ 2 - (2 * (6233 / 12500 : ℝ) + 2 * (753 / 2500 : ℝ) * δ 2) ≤ (0 : ℝ) := by
  have e : theta U δ 2 - (2 * (6233 / 12500 : ℝ) + 2 * (753 / 2500 : ℝ) * δ 2) = (-3091 / 12500 : ℝ) + (0 : ℝ) * δ 0 + (0 : ℝ) * δ 1 + (497 / 1250 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, U] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma bt02 (hδ : InTri R δ) : (theta U δ 2 + (2 * (6233 / 12500 : ℝ) + 2 * (753 / 2500 : ℝ) * δ 2)) / 2 ≤ (24 / 25 : ℝ) := by
  have e : (theta U δ 2 + (2 * (6233 / 12500 : ℝ) + 2 * (753 / 2500 : ℝ) * δ 2)) / 2 = (21841 / 25000 : ℝ) + (0 : ℝ) * δ 0 + (0 : ℝ) * δ 1 + (2003 / 2500 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, U] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma slh1 (hδ : InTri R δ) : theta U δ 1 - (theta U δ 0 + theta U δ 2) ≤ (0 : ℝ) := by
  have e : theta U δ 1 - (theta U δ 0 + theta U δ 2) = (-3 / 4 : ℝ) + (-1 : ℝ) * δ 0 + (1 : ℝ) * δ 1 + (-1 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, U] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma sli10 (hδ : InTri R δ) : theta U δ 0 - (2 * (6233 / 12500 : ℝ) + 2 * (753 / 2500 : ℝ) * δ 0) ≤ (0 : ℝ) := by
  have e : theta U δ 0 - (2 * (6233 / 12500 : ℝ) + 2 * (753 / 2500 : ℝ) * δ 0) = (-3091 / 12500 : ℝ) + (497 / 1250 : ℝ) * δ 0 + (0 : ℝ) * δ 1 + (0 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, U] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma bt10 (hδ : InTri R δ) : (theta U δ 0 + (2 * (6233 / 12500 : ℝ) + 2 * (753 / 2500 : ℝ) * δ 0)) / 2 ≤ (24 / 25 : ℝ) := by
  have e : (theta U δ 0 + (2 * (6233 / 12500 : ℝ) + 2 * (753 / 2500 : ℝ) * δ 0)) / 2 = (21841 / 25000 : ℝ) + (2003 / 2500 : ℝ) * δ 0 + (0 : ℝ) * δ 1 + (0 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, U] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma sli12 (hδ : InTri R δ) : theta U δ 2 - (2 * (6233 / 12500 : ℝ) + 2 * (753 / 2500 : ℝ) * δ 2) ≤ (0 : ℝ) := by
  have e : theta U δ 2 - (2 * (6233 / 12500 : ℝ) + 2 * (753 / 2500 : ℝ) * δ 2) = (-3091 / 12500 : ℝ) + (0 : ℝ) * δ 0 + (0 : ℝ) * δ 1 + (497 / 1250 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, U] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma bt12 (hδ : InTri R δ) : (theta U δ 2 + (2 * (6233 / 12500 : ℝ) + 2 * (753 / 2500 : ℝ) * δ 2)) / 2 ≤ (24 / 25 : ℝ) := by
  have e : (theta U δ 2 + (2 * (6233 / 12500 : ℝ) + 2 * (753 / 2500 : ℝ) * δ 2)) / 2 = (21841 / 25000 : ℝ) + (0 : ℝ) * δ 0 + (0 : ℝ) * δ 1 + (2003 / 2500 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, U] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma slh2 (hδ : InTri R δ) : theta U δ 2 - (theta U δ 0 + theta U δ 1) ≤ (0 : ℝ) := by
  have e : theta U δ 2 - (theta U δ 0 + theta U δ 1) = (-3 / 4 : ℝ) + (-1 : ℝ) * δ 0 + (-1 : ℝ) * δ 1 + (1 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, U] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma sli20 (hδ : InTri R δ) : theta U δ 0 - (2 * (6233 / 12500 : ℝ) + 2 * (753 / 2500 : ℝ) * δ 0) ≤ (0 : ℝ) := by
  have e : theta U δ 0 - (2 * (6233 / 12500 : ℝ) + 2 * (753 / 2500 : ℝ) * δ 0) = (-3091 / 12500 : ℝ) + (497 / 1250 : ℝ) * δ 0 + (0 : ℝ) * δ 1 + (0 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, U] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma bt20 (hδ : InTri R δ) : (theta U δ 0 + (2 * (6233 / 12500 : ℝ) + 2 * (753 / 2500 : ℝ) * δ 0)) / 2 ≤ (24 / 25 : ℝ) := by
  have e : (theta U δ 0 + (2 * (6233 / 12500 : ℝ) + 2 * (753 / 2500 : ℝ) * δ 0)) / 2 = (21841 / 25000 : ℝ) + (2003 / 2500 : ℝ) * δ 0 + (0 : ℝ) * δ 1 + (0 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, U] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma sli21 (hδ : InTri R δ) : theta U δ 1 - (2 * (6233 / 12500 : ℝ) + 2 * (753 / 2500 : ℝ) * δ 1) ≤ (0 : ℝ) := by
  have e : theta U δ 1 - (2 * (6233 / 12500 : ℝ) + 2 * (753 / 2500 : ℝ) * δ 1) = (-3091 / 12500 : ℝ) + (0 : ℝ) * δ 0 + (497 / 1250 : ℝ) * δ 1 + (0 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, U] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])

lemma bt21 (hδ : InTri R δ) : (theta U δ 1 + (2 * (6233 / 12500 : ℝ) + 2 * (753 / 2500 : ℝ) * δ 1)) / 2 ≤ (24 / 25 : ℝ) := by
  have e : (theta U δ 1 + (2 * (6233 / 12500 : ℝ) + 2 * (753 / 2500 : ℝ) * δ 1)) / 2 = (21841 / 25000 : ℝ) + (0 : ℝ) * δ 0 + (2003 / 2500 : ℝ) * δ 1 + (0 : ℝ) * δ 2 := by
    simp [tariff, star, other, theta, U] <;> ring
  rw [e]
  exact tri3_affine_le R_pos hδ (by norm_num [R]) (by norm_num [R]) (by norm_num [R])


lemma slope_all (hδ : InTri R δ) (h i : Fin 3) (e : ℝ) (he : 0 ≤ e) :
    NNN13.rawSlope (theta U δ) (parentsH U h e δ) i ≤ 0 := by
  fin_cases h <;> fin_cases i <;>
    simp [NNN13.rawSlope, NNN13.cross, parentsH, star, other, tariff] <;>
    first
    | (have := slh0 hδ; simp [theta, U] at this ⊢; linarith)
    | (have := slh1 hδ; simp [theta, U] at this ⊢; linarith)
    | (have := slh2 hδ; simp [theta, U] at this ⊢; linarith)
    | (have := sli01 hδ; simp [theta, U] at this ⊢; linarith)
    | (have := sli02 hδ; simp [theta, U] at this ⊢; linarith)
    | (have := sli10 hδ; simp [theta, U] at this ⊢; linarith)
    | (have := sli12 hδ; simp [theta, U] at this ⊢; linarith)
    | (have := sli20 hδ; simp [theta, U] at this ⊢; linarith)
    | (have := sli21 hδ; simp [theta, U] at this ⊢; linarith)

lemma beta_all (hδ : InTri R δ) (h i : Fin 3) (e : ℝ) (hi : i ≠ h) (he0 : 0 ≤ e)
    (he : e ≤ 1 / 25) : betaPackH U h e δ i ≤ 1 := by
  fin_cases h <;> fin_cases i <;> simp at hi <;>
    simp [betaPackH, parentsH, cross, tariff, other] <;>
    first
    | (have := bt01 hδ; simp [theta, U] at this ⊢; linarith)
    | (have := bt02 hδ; simp [theta, U] at this ⊢; linarith)
    | (have := bt10 hδ; simp [theta, U] at this ⊢; linarith)
    | (have := bt12 hδ; simp [theta, U] at this ⊢; linarith)
    | (have := bt20 hδ; simp [theta, U] at this ⊢; linarith)
    | (have := bt21 hδ; simp [theta, U] at this ⊢; linarith)

/-- The track facts of U. -/
def facts : TrackFacts U where
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
  form_ord := fun δ hδ h x hx => (formH_U h hδ.1 hδ.2 hx).1
  form_pack := fun δ hδ h x hx => (formH_U h hδ.1 hδ.2 hx).2

end OM.NNN18.FactsU
