import Lib.OM.NNN12.BranchMoments
import Lib.OM.NNN12.Scalar

/-! Generic capacity fallback and balancing algebra for mixed raw networks. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN12
set_option maxHeartbeats 1500000

def rawCapacity (q k : ℕ) (t : ℝ) : ℝ :=
  Real.logb 2 q - Real.logb 2 (1 + (q - 1 : ℝ) * (2 : ℝ) ^ (k * (2 * t - 9 / 4)))

lemma rawCapacity_le {q : ℕ} [Fact q.Prime] (k : ℕ) (t : ℝ) :
    rawCapacity q k t ≤ Real.logb 2 q := by
  have hq : 0 ≤ (q - 1 : ℝ) := sub_nonneg.mpr (alphabet_one_le (q := q))
  have hl : 0 ≤ Real.logb 2 (1 + (q - 1 : ℝ) * (2 : ℝ) ^ (k * (2 * t - 9 / 4))) :=
    Real.logb_nonneg (by norm_num) (le_add_of_nonneg_right (by positivity))
  dsimp [rawCapacity]
  linarith

lemma raw_moment_eq (q k N m : ℕ) (S t : ℝ) :
    momentExponent q N (m * S) (k * (2 * t - 9 / 4)) = m * S - N * rawCapacity q k t := by
  dsimp [momentExponent, rawCapacity]
  ring

lemma rawCapacity7 (t : ℝ) : rawCapacity 7 2 t = NNN11.codeK t := by
  dsimp [rawCapacity, NNN11.codeK]
  congr 2 <;> norm_num <;> congr 1 <;> ring

lemma balanced_clipped_head {I : Type} [Fintype I] (t L M m : I → ℝ) (p A : ℝ)
    (ht : ∀ i, 0 ≤ t i)
    (he : (∑ i, t i * L i) + (∑ i, t i * M i) = (p + ∑ i, t i * m i) * A) :
    (∑ i, t i * (L i - max 0 (m i * A - M i))) ≤ p * A := by
  have hle : (∑ i, t i * (L i - max 0 (m i * A - M i))) ≤
      ∑ i, t i * (L i - (m i * A - M i)) := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (sub_le_sub_left (le_max_right 0 _) _) (ht i)
  apply hle.trans_eq
  have hr : (∑ i, t i * (L i - (m i * A - M i))) =
      (∑ i, t i * L i) - (∑ i, t i * m i) * A + (∑ i, t i * M i) := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hr]
  nlinarith only [he]

lemma retained_scalar_exponent {s A C : ℝ} {h m : ℕ} (hh : 0 < h) (hm : 0 < m)
    (hC : C ≤ (2 : ℝ) ^ h)
    (hs : s ^ (h + m) ≤ C * (2 : ℝ) ^ ((h + m : ℕ) * A) +
      s ^ h * (2 : ℝ) ^ ((m : ℝ) * A)) : s ≤ 2 * (2 : ℝ) ^ A := by
  apply retained_scalar_scaled (h := h) (m := m) (by positivity) hh hm hC
  have he (n : ℕ) : ((2 : ℝ) ^ A) ^ n = (2 : ℝ) ^ ((n : ℝ) * A) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm]
  simpa only [he] using! hs

end OM.NNN12
