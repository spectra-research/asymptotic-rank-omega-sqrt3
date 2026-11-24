import Lib.OM.NNN13.Packing
import Lib.OM.NNN13.Potential

/-! Analytic shape reduction for a fixed policy. Its source gap is a linear
form plus nonnegative multiples of the three-capacity packing function.
Consequently three exact vertex checks cover a whole shape triangle,
including capacity switches and degenerate faces. -/
noncomputable section
open scoped BigOperators
namespace OM.NNN13

def shapeGap {ι : Type*} [Fintype ι] (g : Fin 3 → ℝ) (w k : ι → ℝ)
    (A B : ι → Fin 3 → ℝ) (x : Fin 3 → ℝ) : ℝ :=
  plane g x + ∑ i, w i * capacity (k i) (plane (A i) x) (plane (B i) x)

theorem shapeGap_mix {ι : Type*} [Fintype ι] (g : Fin 3 → ℝ) (w k : ι → ℝ)
    (A B : ι → Fin 3 → ℝ) (hw : ∀ i, 0 ≤ w i) (hk : ∀ i, 0 < k i)
    (x y : Fin 3 → ℝ) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    s * shapeGap g w k A B x + t * shapeGap g w k A B y ≤
      shapeGap g w k A B (fun j => s * x j + t * y j) := by
  have hi (i : ι) := mul_le_mul_of_nonneg_left
    (capacity_mix (hk i) hs ht (plane (A i) x) (plane (B i) x)
      (plane (A i) y) (plane (B i) y)) (hw i)
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
  simp only [shapeGap, plane_mix]
  have he : (∑ i, w i * (s * capacity (k i) (plane (A i) x) (plane (B i) x) +
      t * capacity (k i) (plane (A i) y) (plane (B i) y))) =
      s * (∑ i, w i * capacity (k i) (plane (A i) x) (plane (B i) x)) +
      t * (∑ i, w i * capacity (k i) (plane (A i) y) (plane (B i) y)) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he] at hh
  nlinarith only [hh]

/-- The nonnegative cone version is stronger than the normalized triangle
statement; weights need not sum to one. -/
theorem shapeGap_triangle {ι : Type*} [Fintype ι] (g : Fin 3 → ℝ) (w k : ι → ℝ)
    (A B : ι → Fin 3 → ℝ) (hw : ∀ i, 0 ≤ w i) (hk : ∀ i, 0 < k i)
    (x y z : Fin 3 → ℝ) {s t u : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hu : 0 ≤ u)
    (hx : 0 ≤ shapeGap g w k A B x) (hy : 0 ≤ shapeGap g w k A B y)
    (hz : 0 ≤ shapeGap g w k A B z) :
    0 ≤ shapeGap g w k A B (fun j => s * x j + t * y j + u * z j) := by
  have hxy := shapeGap_mix g w k A B hw hk x y hs ht
  have hxyz := shapeGap_mix g w k A B hw hk (fun j => s * x j + t * y j) z
    (by norm_num : (0 : ℝ) ≤ 1) hu
  simp only [one_mul] at hxyz
  have hpos := add_nonneg (mul_nonneg hs hx) (mul_nonneg ht hy)
  have hzpos := mul_nonneg hu hz
  linarith only [hxy, hxyz, hpos, hzpos]

/-- The candidate is concave in shape, without any ordering of tensor legs. -/
theorem potential_mix (r z : ℝ) (x y : Fin 3 → ℝ) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    s * potential r z x + t * potential r z y ≤
      potential r z (fun i => s * x i + t * y i) := by
  have hS := min3_mix (fun i => plane (starCoefficients (profile r z) i) x)
    (fun i => plane (starCoefficients (profile r z) i) y) hs ht
  have hP := min3_mix (fun i => plane (candidateCoefficients r z i) x)
    (fun i => plane (candidateCoefficients r z i) y) hs ht
  have hxS := mul_le_mul_of_nonneg_left (min_le_left
    (min3 (fun i => plane (starCoefficients (profile r z) i) x))
    (min3 (fun i => plane (candidateCoefficients r z i) x))) hs
  have hyS := mul_le_mul_of_nonneg_left (min_le_left
    (min3 (fun i => plane (starCoefficients (profile r z) i) y))
    (min3 (fun i => plane (candidateCoefficients r z i) y))) ht
  have hxP := mul_le_mul_of_nonneg_left (min_le_right
    (min3 (fun i => plane (starCoefficients (profile r z) i) x))
    (min3 (fun i => plane (candidateCoefficients r z i) x))) hs
  have hyP := mul_le_mul_of_nonneg_left (min_le_right
    (min3 (fun i => plane (starCoefficients (profile r z) i) y))
    (min3 (fun i => plane (candidateCoefficients r z i) y))) ht
  have hb : s * basePotential r z x + t * basePotential r z y ≤
      basePotential r z (fun i => s * x i + t * y i) := by
    simp only [basePotential, plane_mix]
    exact le_min (by linarith only [hS, hxS, hyS]) (by linarith only [hP, hxP, hyP])
  dsimp [potential]
  nlinarith only [hb]

end OM.NNN13
