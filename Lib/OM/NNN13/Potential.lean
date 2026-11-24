import Lib.OM.NNN13.Recursion
import Lib.OM.NNN12.Profiles

/-! The filed six-plane candidate, with the uniform lift allowed by the
703/500 target. These are properties of the candidate, not a claim that
its recursive supersolution inequalities have been established. -/
noncomputable section
namespace OM.NNN13
set_option maxHeartbeats 1000000

def plane (c x : Fin 3 → ℝ) : ℝ := c 0 * x 0 + c 1 * x 1 + c 2 * x 2
def min3 (f : Fin 3 → ℝ) : ℝ := min (f 0) (min (f 1) (f 2))

lemma min3_le (f : Fin 3 → ℝ) (i : Fin 3) : min3 f ≤ f i := by
  fin_cases i
  · exact min_le_left _ _
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)

lemma le_min3 {a : ℝ} {f : Fin 3 → ℝ} (h : ∀ i, a ≤ f i) : a ≤ min3 f :=
  le_min (h 0) (le_min (h 1) (h 2))

lemma plane_nonneg {c x : Fin 3 → ℝ} (hc : ∀ i, 0 ≤ c i) (hx : ∀ i, 0 ≤ x i) :
    0 ≤ plane c x :=
  add_nonneg (add_nonneg (mul_nonneg (hc 0) (hx 0)) (mul_nonneg (hc 1) (hx 1)))
    (mul_nonneg (hc 2) (hx 2))

lemma plane_scale (c x : Fin 3 → ℝ) (s : ℝ) :
    plane c (fun i => s * x i) = s * plane c x := by unfold plane; ring

lemma plane_mix (c x y : Fin 3 → ℝ) (s t : ℝ) :
    plane c (fun i => s * x i + t * y i) = s * plane c x + t * plane c y := by
  unfold plane
  ring

lemma min3_scale {s : ℝ} (hs : 0 ≤ s) (f : Fin 3 → ℝ) :
    min3 (fun i => s * f i) = s * min3 f := by
  simp only [min3, mul_min_of_nonneg _ _ hs]

lemma min3_mix (f g : Fin 3 → ℝ) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    s * min3 f + t * min3 g ≤ min3 (fun i => s * f i + t * g i) := by
  apply le_min3
  intro i
  exact add_le_add (mul_le_mul_of_nonneg_left (min3_le f i) hs)
    (mul_le_mul_of_nonneg_left (min3_le g i) ht)

def a : ℝ := 40157 / 100000
def b : ℝ := 100281 / 200000
def tiltA : ℝ := 7 / 25
def tiltB : ℝ := -1607 / 25000
def tiltG : ℝ := 629 / 2000
def tiltE : ℝ := (tiltG - tiltA - 2 * tiltB) / 3
def beta : ℝ := 703 / 500
def lift : ℝ := 27 / 50000
def radius : ℝ := 7 / 200

/-- `z = r*s` avoids products of independent interval variables. -/
def deviation (r z : ℝ) : Fin 3 → ℝ := ![r, -r / 2 + 3 * z / 2, -r / 2 - 3 * z / 2]
def profile (r z : ℝ) (i : Fin 3) : ℝ := 3 / 4 + deviation r z i
def candidateCoefficients (r z : ℝ) : Fin 3 → Fin 3 → ℝ :=
  let v := deviation r z
  ![![a + tiltA * r + tiltE * v 0,
      b + tiltB * r + tiltG * v 2 + tiltE * v 0,
      b + tiltB * r + tiltG * v 1 + tiltE * v 0],
    ![b + tiltB * r + tiltG * v 2 + tiltE * v 1,
      a + tiltA * r + tiltE * v 1,
      b + tiltB * r + tiltG * v 0 + tiltE * v 1],
    ![b + tiltB * r + tiltG * v 1 + tiltE * v 2,
      b + tiltB * r + tiltG * v 0 + tiltE * v 2,
      a + tiltA * r + tiltE * v 2]]
def starCoefficients (t : Fin 3 → ℝ) : Fin 3 → Fin 3 → ℝ :=
  ![![0, t 2, t 1], ![t 2, 0, t 0], ![t 1, t 0, 0]]
def basePotential (r z : ℝ) (x : Fin 3 → ℝ) : ℝ :=
  min (min3 (fun i => plane (starCoefficients (profile r z) i) x))
    (min3 (fun i => plane (candidateCoefficients r z i) x))
def potential (r z : ℝ) (x : Fin 3 → ℝ) : ℝ :=
  basePotential r z x + lift * (x 0 + x 1 + x 2)
def target (r z : ℝ) (v : NNN12.Shape) : ℝ := potential r z (fun i => (v i : ℝ))

lemma constants : a + 2 * b = 70219 / 50000 ∧ a + 2 * b + 3 * lift = beta ∧
    0 < lift ∧ tiltA + 2 * tiltB = 1893 / 12500 := by
  norm_num [a, b, lift, beta, tiltA, tiltB]

lemma profile_sum (r z : ℝ) : profile r z 0 + profile r z 1 + profile r z 2 = 9 / 4 := by
  dsimp [profile, deviation]
  ring

lemma profile_box {r z : ℝ} (hr : r ∈ Set.Icc 0 radius) (hz : z ∈ Set.Icc 0 r)
    (i : Fin 3) : profile r z i ∈ Set.Icc (1 / 4 : ℝ) 1 := by
  fin_cases i <;> norm_num [profile, deviation, radius] at hr ⊢ <;>
    constructor <;> linarith [hr.1, hr.2, hz.1, hz.2]

lemma candidateCoefficients_nonneg {r z : ℝ} (hr : r ∈ Set.Icc 0 radius)
    (hz : z ∈ Set.Icc 0 r) (i j : Fin 3) : 0 ≤ candidateCoefficients r z i j := by
  fin_cases i <;> fin_cases j <;>
    simp only [candidateCoefficients, deviation, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
    norm_num [a, b, tiltA, tiltB, tiltG, tiltE, radius] at hr ⊢ <;>
    linarith [hr.1, hr.2, hz.1, hz.2]

lemma starCoefficients_nonneg {t : Fin 3 → ℝ} (ht : ∀ i, 0 ≤ t i) (i j : Fin 3) :
    0 ≤ starCoefficients t i j := by
  fin_cases i <;> fin_cases j <;> simp [starCoefficients, ht]

lemma basePotential_le_candidate (r z : ℝ) (x : Fin 3 → ℝ) (i : Fin 3) :
    basePotential r z x ≤ plane (candidateCoefficients r z i) x :=
  (min_le_right _ _).trans (min3_le _ i)

lemma potential_nonneg {r z : ℝ} (hr : r ∈ Set.Icc 0 radius) (hz : z ∈ Set.Icc 0 r)
    {x : Fin 3 → ℝ} (hx : ∀ i, 0 ≤ x i) : 0 ≤ potential r z x := by
  apply add_nonneg
  · apply le_min
    · apply le_min3
      intro i
      apply plane_nonneg (fun j => starCoefficients_nonneg (fun j => ?_) i j) hx
      linarith [(profile_box hr hz j).1]
    · exact le_min3 (fun i => plane_nonneg (candidateCoefficients_nonneg hr hz i) hx)
  · exact mul_nonneg constants.2.2.1.le (add_nonneg (add_nonneg (hx 0) (hx 1)) (hx 2))

lemma potential_scale (r z : ℝ) (x : Fin 3 → ℝ) {s : ℝ} (hs : 0 ≤ s) :
    potential r z (fun i => s * x i) = s * potential r z x := by
  simp only [potential, basePotential, plane_scale, min3_scale hs, ← mul_min_of_nonneg _ _ hs]
  ring

/-- The exact cubic identity survives throughout the entire profile wedge. -/
lemma candidate_cube (r z l : ℝ) (i : Fin 3) :
    plane (candidateCoefficients r z i) (fun _ => l) =
      (a + 2 * b + (tiltA + 2 * tiltB) * (r - deviation r z i)) * l := by
  fin_cases i <;> dsimp [plane, candidateCoefficients, deviation, a, b, tiltA, tiltB, tiltG, tiltE] <;> ring

theorem potential_cube_le (r z l : ℝ) : potential r z (fun _ => l) ≤ beta * l := by
  have hh := basePotential_le_candidate r z (fun _ => l) 0
  rw [candidate_cube] at hh
  simp only [deviation, Matrix.cons_val_zero, sub_self, mul_zero, add_zero] at hh
  dsimp [potential]
  have he := congrArg (fun c : ℝ => c * l) constants.2.1
  nlinarith only [hh, he]

lemma target_nonneg {r z : ℝ} (hr : r ∈ Set.Icc 0 radius) (hz : z ∈ Set.Icc 0 r)
    (v : NNN12.Shape) : 0 ≤ target r z v := potential_nonneg hr hz (fun _ => Nat.cast_nonneg _)

end OM.NNN13
