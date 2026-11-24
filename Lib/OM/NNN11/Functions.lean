import Lib.OM.NNN8.Numerics

noncomputable section
namespace OM.NNN11

def codeK (t : ℝ) : ℝ :=
  Real.logb 2 7 - Real.logb 2 (1 + 6 * (2 : ℝ) ^ (4 * t - 9 / 2))

def codeP (t : ℝ) : ℝ :=
  6 * (2 : ℝ) ^ (4 * t - 9 / 2) / (1 + 6 * (2 : ℝ) ^ (4 * t - 9 / 2))

def shortParam (t : ℝ) : ℝ := (9 / 4 - t) / 2
def weightedK (t : ℝ) : ℝ := t * codeK t
def capacity (t : ℝ) : ℝ := 7 * weightedK t + 13 * weightedK (shortParam t)
def denominator (t : ℝ) : ℝ := 196 + 14 * t
def numeratorF (t : ℝ) : ℝ := -98 * t ^ 2 + 161 * t + 1953 / 8 - capacity t
def numeratorG (t : ℝ) : ℝ := -126 * t ^ 2 + 623 / 2 * t + 189 / 4 - capacity t
def innerF (t : ℝ) : ℝ := numeratorF t / denominator t
def innerG (t : ℝ) : ℝ := numeratorG t / denominator t
def outerA (t : ℝ) : ℝ := 59 / 100 * (9 / 4 - t) + 41 / 100 * innerF t
def outerD (t : ℝ) : ℝ := 59 / 100 * (2 * t - 9 / 4) + 41 / 100 * (t - innerG t)
def fullMoment (t : ℝ) : ℝ :=
  70 * outerA t + 7 * (Real.logb 2 (1 + 6 * (2 : ℝ) ^ (2 * outerD t)) - Real.logb 2 7)
def lastMoment (t : ℝ) : ℝ := 42 * (9 / 4 - t) - 6 * codeK t
def beta : ℝ := (105 + 3 / 2 * fullMoment (3 / 4) + 3 / 4 * lastMoment (3 / 4)) / (413 / 2)

lemma codeK_eq_log_ratio (t : ℝ) :
    codeK t = Real.logb 2 (7 / (1 + 6 * (2 : ℝ) ^ (4 * t - 9 / 2))) := by
  rw [Real.logb_div (by norm_num : (7 : ℝ) ≠ 0) (by positivity)]
  rfl

lemma denominator_pos {t : ℝ} (ht : 0 ≤ t) : 0 < denominator t := by
  dsimp [denominator]
  linarith

lemma shortParam_mem {t : ℝ} (ht : t ∈ Set.Icc (1 / 4 : ℝ) 1) :
    shortParam t ∈ Set.Icc (1 / 4 : ℝ) 1 := by
  dsimp [shortParam]
  constructor <;> linarith [ht.1, ht.2]

lemma numeratorF_paper (t : ℝ) :
    numeratorF t = 91 / 2 * (9 / 4) + 7 / 2 * t + 56 * (9 / 4) ^ 2 +
      14 * (9 / 4) * t - 70 * t ^ 2 - 112 * shortParam t ^ 2 - capacity t := by
  dsimp [numeratorF, shortParam]
  ring

lemma numeratorG_paper (t : ℝ) :
    numeratorG t = 21 * (9 / 4) + 28 * t + 126 * t * (9 / 4 - t) - capacity t := by
  dsimp [numeratorG]
  ring

lemma innerF_sub_innerG {t : ℝ} (ht : 0 ≤ t) :
    innerF t - innerG t = (4 * t - 9) * (8 * t - 25) / (16 * (t + 14)) := by
  have hd := (denominator_pos ht).ne'
  dsimp [innerF, innerG, numeratorF, numeratorG, denominator] at *
  have ht' : t + 14 ≠ 0 := by linarith
  field_simp
  ring

lemma innerF_balance : innerF (3 / 4) = 3 / 2 - 30 * codeK (3 / 4) / 413 := by
  norm_num [innerF, numeratorF, denominator, capacity, weightedK, shortParam]
  ring

lemma innerG_balance : innerG (3 / 4) = (420 - 30 * codeK (3 / 4)) / 413 := by
  norm_num [innerG, numeratorG, denominator, capacity, weightedK, shortParam]
  ring

lemma beta_balance :
    70 * beta + (3 / 4) * (2 * (70 * beta - fullMoment (3 / 4)) +
      (42 * beta - lastMoment (3 / 4))) = 105 := by
  dsimp [beta]
  ring

end OM.NNN11
