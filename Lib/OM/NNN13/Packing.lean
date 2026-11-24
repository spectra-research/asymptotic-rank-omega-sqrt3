import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic

noncomputable section
namespace OM.NNN13

def capacity (k A B : ℝ) : ℝ :=
  min ((A + B) / (2 * k + 1)) (min (A / k) (B / k))

lemma capacity_nonneg {k A B : ℝ} (hk : 0 < k) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ capacity k A B := by
  unfold capacity
  positivity

lemma le_capacity_iff {k A B N : ℝ} (hk : 0 < k) :
    N ≤ capacity k A B ↔
      (2 * k + 1) * N ≤ A + B ∧ k * N ≤ A ∧ k * N ≤ B := by
  simp only [capacity, le_min_iff, le_div_iff₀ hk,
    le_div_iff₀ (show 0 < 2 * k + 1 by linarith)]
  constructor <;> rintro ⟨h, hA, hB⟩ <;> constructor
  · nlinarith only [h]
  · constructor <;> nlinarith only [hA, hB]
  · nlinarith only [h]
  · constructor <;> nlinarith only [hA, hB]

/-- No feasible pair of orientations exceeds the three-capacity minimum. -/
theorem packing_upper {k A B u v : ℝ} (hk : 0 < k) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hA : k * u + (k + 1) * v ≤ A) (hB : (k + 1) * u + k * v ≤ B) :
    u + v ≤ capacity k A B := by
  rw [le_capacity_iff hk]
  constructor
  · nlinarith only [hA, hB]
  · constructor <;> nlinarith only [hA, hB, hu, hv]

/-- An explicit feasible interval witnesses every nonnegative length up to capacity. -/
theorem packing_exists {k A B N : ℝ} (hk : 0 < k) (hN : 0 ≤ N)
    (hcap : N ≤ capacity k A B) :
    ∃ u v : ℝ, 0 ≤ u ∧ 0 ≤ v ∧ u + v = N ∧
      k * u + (k + 1) * v ≤ A ∧ (k + 1) * u + k * v ≤ B := by
  obtain ⟨hT, hA, hB⟩ := (le_capacity_iff hk).1 hcap
  let u := max 0 ((k + 1) * N - A)
  have hu : 0 ≤ u := le_max_left _ _
  have huN : u ≤ N := max_le hN (by nlinarith only [hA])
  have huA : (k + 1) * N - A ≤ u := le_max_right _ _
  have huB : u ≤ B - k * N := max_le (by linarith only [hB])
    (by nlinarith only [hT])
  refine ⟨u, N - u, hu, sub_nonneg.mpr huN, by ring, ?_, ?_⟩
  · nlinarith only [huA]
  · nlinarith only [huB]

theorem packing_optimal {k A B : ℝ} (hk : 0 < k) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ u v : ℝ, 0 ≤ u ∧ 0 ≤ v ∧ u + v = capacity k A B ∧
      k * u + (k + 1) * v ≤ A ∧ (k + 1) * u + k * v ≤ B :=
  packing_exists hk (capacity_nonneg hk hA hB) le_rfl

/-- Integer realizations lose strictly fewer than two cycles, including zero supplies. -/
theorem packing_integer {k A B : ℕ} (hk : 0 < k) :
    ∃ u v : ℕ, k * u + (k + 1) * v ≤ A ∧ (k + 1) * u + k * v ≤ B ∧
      (u + v : ℝ) ≤ capacity k A B ∧ capacity k A B < (u + v : ℝ) + 2 := by
  have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  obtain ⟨u, v, hu, hv, huv, hA, hB⟩ :=
    packing_optimal hk' (Nat.cast_nonneg A) (Nat.cast_nonneg B)
  have hfu := Nat.floor_le hu
  have hfv := Nat.floor_le hv
  have hAu : (k : ℝ) * ⌊u⌋₊ ≤ k * u := mul_le_mul_of_nonneg_left hfu hk'.le
  have hAv : ((k : ℝ) + 1) * ⌊v⌋₊ ≤ (k + 1) * v :=
    mul_le_mul_of_nonneg_left hfv (by positivity)
  have hBu : ((k : ℝ) + 1) * ⌊u⌋₊ ≤ (k + 1) * u :=
    mul_le_mul_of_nonneg_left hfu (by positivity)
  have hBv : (k : ℝ) * ⌊v⌋₊ ≤ k * v := mul_le_mul_of_nonneg_left hfv hk'.le
  refine ⟨⌊u⌋₊, ⌊v⌋₊, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast (show (k : ℝ) * ⌊u⌋₊ + (k + 1) * ⌊v⌋₊ ≤ A by linarith)
  · exact_mod_cast (show ((k : ℝ) + 1) * ⌊u⌋₊ + k * ⌊v⌋₊ ≤ B by linarith)
  · linarith
  · linarith [Nat.lt_floor_add_one u, Nat.lt_floor_add_one v]

lemma capacity_mono {k A B A' B' : ℝ} (hk : 0 < k) (hA : A ≤ A') (hB : B ≤ B') :
    capacity k A B ≤ capacity k A' B' := by
  obtain ⟨hT, hL, hR⟩ := (le_capacity_iff hk).1 (le_refl (capacity k A B))
  exact (le_capacity_iff hk).2 ⟨by linarith, hL.trans hA, hR.trans hB⟩

lemma capacity_homogeneous {s : ℝ} (hs : 0 ≤ s) (k A B : ℝ) :
    capacity k (s * A) (s * B) = s * capacity k A B := by
  simp only [capacity, ← mul_add, mul_div_assoc, mul_min_of_nonneg _ _ hs]

/-- Concavity supplies the all-shape implication from vertex checks. -/
theorem capacity_mix {k s t : ℝ} (hk : 0 < k) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (A B A' B' : ℝ) :
    s * capacity k A B + t * capacity k A' B' ≤
      capacity k (s * A + t * A') (s * B + t * B') := by
  obtain ⟨hT, hA, hB⟩ := (le_capacity_iff hk).1 (le_refl (capacity k A B))
  obtain ⟨hT', hA', hB'⟩ := (le_capacity_iff hk).1 (le_refl (capacity k A' B'))
  rw [le_capacity_iff hk]
  constructor
  · nlinarith only [mul_le_mul_of_nonneg_left hT hs, mul_le_mul_of_nonneg_left hT' ht]
  · constructor
    · nlinarith only [mul_le_mul_of_nonneg_left hA hs, mul_le_mul_of_nonneg_left hA' ht]
    · nlinarith only [mul_le_mul_of_nonneg_left hB hs, mul_le_mul_of_nonneg_left hB' ht]

/-- A nonpositive logarithmic moment turns the concave capacity into a convex cost. -/
theorem capacity_cost_mix {k s t L : ℝ} (hk : 0 < k) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hL : L ≤ 0) (A B A' B' : ℝ) :
    L * capacity k (s * A + t * A') (s * B + t * B') ≤
      s * (L * capacity k A B) + t * (L * capacity k A' B') := by
  have hh := mul_le_mul_of_nonpos_left (capacity_mix hk hs ht A B A' B') hL
  nlinarith only [hh]

end OM.NNN13
