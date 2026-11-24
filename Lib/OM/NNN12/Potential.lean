import Lib.OM.NNN11.Functions

noncomputable section
namespace OM.NNN12

def a : ℝ := 836693 / 2000000
def b : ℝ := 1016213 / 2000000
def c : ℝ := 481083 / 1000000
def eta : ℝ := 125473 / 2000000
def alpha : ℝ := 87971 / 62500
def upper : ℝ := 1881 / 2500
def lower : ℝ := 1863 / 2500
def gamma : ℝ := 9 / 13

lemma coefficients : 0 < a ∧ a < c ∧ c < b ∧ eta = c - a ∧
    a + b + c = alpha ∧ alpha < 176 / 125 ∧ 0 < gamma ∧ gamma < 1 := by
  norm_num [a, b, c, eta, alpha, gamma]

def largest (x y z : ℝ) : ℝ := max x (max y z)
def smallest (x y z : ℝ) : ℝ := min x (min y z)
def middle (x y z : ℝ) : ℝ := x + y + z - largest x y z - smallest x y z
def affine (x y z : ℝ) : ℝ := a * x + b * y + c * z
def potential (x y z : ℝ) : ℝ := affine (largest x y z) (middle x y z) (smallest x y z)
def fallbackPotential (x y z : ℝ) : ℝ :=
  min (potential x y z) (upper * (x + y + z - largest x y z))

lemma largest_le_sum {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    largest x y z ≤ x + y + z := by
  exact max_le (by linarith) (max_le (by linarith) (by linarith))

lemma middle_nonneg {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    0 ≤ middle x y z := by
  unfold middle largest smallest
  simp only [max_def, min_def]
  split_ifs <;> linarith

lemma potential_nonneg {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    0 ≤ potential x y z := by
  have hh : 0 ≤ largest x y z := hx.trans (le_max_left _ _)
  have hl : 0 ≤ smallest x y z := le_min hx (le_min hy hz)
  have hm := middle_nonneg hx hy hz
  unfold potential affine
  have ha : 0 ≤ a := by norm_num [a]
  have hb : 0 ≤ b := by norm_num [b]
  have hc : 0 ≤ c := by norm_num [c]
  positivity

lemma fallbackPotential_nonneg {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    0 ≤ fallbackPotential x y z := by
  exact le_min (potential_nonneg hx hy hz)
    (mul_nonneg (by norm_num [upper]) (sub_nonneg.mpr (largest_le_sum hx hy hz)))

lemma potential_sorted {x y z : ℝ} (hxy : y ≤ x) (hyz : z ≤ y) :
    potential x y z = affine x y z := by
  simp [potential, middle, largest, smallest, max_eq_left hxy, max_eq_left hyz,
    min_eq_right (hyz.trans hxy), min_eq_right hyz]
  congr 1 <;> ring

lemma fallbackPotential_sorted {x y z : ℝ} (hxy : y ≤ x) (hyz : z ≤ y) :
    fallbackPotential x y z = min (affine x y z) (upper * (y + z)) := by
  rw [fallbackPotential, potential_sorted hxy hyz]
  simp only [largest, max_eq_left hyz, max_eq_left hxy]
  congr 2
  ring

lemma potential_cube (x : ℝ) : potential x x x = alpha * x := by
  rw [potential_sorted le_rfl le_rfl]
  dsimp [affine, a, b, c, alpha]
  ring

lemma fallbackPotential_cube {x : ℝ} (hx : 0 ≤ x) :
    fallbackPotential x x x = alpha * x := by
  rw [fallbackPotential_sorted le_rfl le_rfl]
  have ha : affine x x x = alpha * x := by rw [← potential_sorted le_rfl le_rfl, potential_cube]
  rw [ha, min_eq_left]
  dsimp [alpha, upper]
  linarith

lemma potential_homogeneous {q : ℝ} (hq : 0 ≤ q) (x y z : ℝ) :
    potential (q * x) (q * y) (q * z) = q * potential x y z := by
  simp only [potential, affine, middle, largest, smallest,
    ← mul_max_of_nonneg _ _ hq, ← mul_min_of_nonneg _ _ hq]
  ring

lemma fallbackPotential_homogeneous {q : ℝ} (hq : 0 ≤ q) (x y z : ℝ) :
    fallbackPotential (q * x) (q * y) (q * z) = q * fallbackPotential x y z := by
  rw [fallbackPotential, potential_homogeneous hq]
  simp only [largest, ← mul_max_of_nonneg _ _ hq]
  have he : upper * (q * x + q * y + q * z - q * max x (max y z)) =
      q * (upper * (x + y + z - max x (max y z))) := by ring
  rw [he, ← mul_min_of_nonneg _ _ hq]
  rfl

end OM.NNN12
