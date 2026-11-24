import Lib.OM.NNN12.Moments
import Lib.OM.NNN12.Excess

noncomputable section
open scoped BigOperators
namespace OM.NNN13

def gamma : ℝ := 9 / 13

lemma gamma_bounds : 0 ≤ gamma ∧ gamma < 1 := by norm_num [gamma]

/-- The sum of recursive degrees is controlled even for a subset of active bonds. -/
lemma recursive_mass_le {ι : Type*} [Fintype ι] {p : ℝ} (t m : ι → ℝ)
    (ht : ∀ i, 0 ≤ t i) (hm : ∀ i, m i ≤ p) (hs : ∑ i, t i ≤ 9 / 4)
    (hp : 0 ≤ p) : (∑ i, t i * m i) ≤ p * (9 / 4) := by
  calc
    (∑ i, t i * m i) ≤ ∑ i, t i * p :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hm i) (ht i))
    _ = (∑ i, t i) * p := (Finset.sum_mul ..).symm
    _ ≤ p * (9 / 4) := by nlinarith only [mul_le_mul_of_nonneg_right hs hp]

theorem combined_contraction {p M : ℝ} (hp : 0 < p) (hM : 0 ≤ M)
    (hbound : M ≤ p * (9 / 4)) : M / (p + M) ≤ gamma := by
  apply (div_le_iff₀ (by positivity : 0 < p + M)).2
  dsimp [gamma]
  linarith

lemma combined_error_payment {p M ε V : ℝ} (hbound : M ≤ p * (9 / 4))
    (hε : 0 ≤ ε) (hV : 0 ≤ V) : M * (ε * V) ≤ (p + M) * (gamma * ε * V) := by
  have hh : M ≤ (p + M) * gamma := by dsimp [gamma]; linarith
  have he := mul_le_mul_of_nonneg_right hh (mul_nonneg hε hV)
  nlinarith only [he]

/-- The zero-word gate is preserved after adding the worst-excess charge.
This applies equally to full and retained recursive groups. -/
theorem recursive_rate_cap {m P B C ε V : ℝ} (hm : 0 ≤ m) (hC : 0 ≤ C)
    (hcap : m * P ≤ B + C) (hε : 0 ≤ ε) (hV : 0 ≤ V) :
    max 0 (m * (P + gamma * ε * V) - (B + m * ε * V)) ≤ C := by
  apply max_le hC
  have hh : 0 ≤ m * ε * V := mul_nonneg (mul_nonneg hm hε) hV
  dsimp [gamma]
  nlinarith only [hcap, hh]

/-- All clipped rates are simultaneously affordable in the physical head. -/
theorem recursive_head_affordable {ι : Type*} [Fintype ι]
    (t m B : ι → ℝ) {p H P ε V : ℝ}
    (ht : ∀ i, 0 ≤ t i) (hε : 0 ≤ ε) (hV : 0 ≤ V)
    (hmass : (∑ i, t i * m i) ≤ p * (9 / 4))
    (hsuper : H + ∑ i, t i * B i ≤ (p + ∑ i, t i * m i) * P) :
    H - ∑ i, t i * max 0 (m i * (P + gamma * ε * V) - (B i + m i * ε * V)) ≤
      p * (P + gamma * ε * V) := by
  have hclip := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => mul_le_mul_of_nonneg_left
      (le_max_right 0 (m i * (P + gamma * ε * V) - (B i + m i * ε * V))) (ht i))
  have heq : (∑ i, t i * (m i * (P + gamma * ε * V) - (B i + m i * ε * V))) =
      (∑ i, t i * m i) * (P + gamma * ε * V) -
        (∑ i, t i * B i) - (∑ i, t i * m i) * (ε * V) := by
    simp only [Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [heq] at hclip
  have herr := combined_error_payment hmass hε hV
  nlinarith only [hclip, herr, hsuper]

/-- A complete finite binomial moment contains its zero word. This proves
the capacity inequality for the actual integer cycle count. -/
lemma moment_capacity {q : ℕ} [Fact q.Prime] (N : ℕ) (A D : ℝ) :
    A ≤ NNN12.momentExponent q N A D + N * Real.logb 2 q := by
  have hq : 0 ≤ (q : ℝ) - 1 := sub_nonneg.mpr NNN12.alphabet_one_le
  have hb : (1 : ℝ) ≤ 1 + (q - 1 : ℝ) * (2 : ℝ) ^ D :=
    le_add_of_nonneg_right (mul_nonneg hq (by positivity))
  have hl : 0 ≤ Real.logb 2 (1 + (q - 1 : ℝ) * (2 : ℝ) ^ D) := by
    have hh := (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 1) (by positivity)).2 hb
    simpa using! hh
  have hn := mul_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N) hl
  dsimp [NNN12.momentExponent]
  nlinarith only [hn]

theorem recursive_code_legal {q : ℕ} [Fact q.Prime] (N : ℕ)
    {A D m P ε V : ℝ} (hm : 0 ≤ m) (hbase : m * P ≤ A)
    (hε : 0 ≤ ε) (hV : 0 ≤ V) :
    NNN12.codeDimension q
      (max 0 (m * (P + gamma * ε * V) -
        (NNN12.momentExponent q N A D + m * ε * V))) ≤ N := by
  apply NNN12.codeDimension_le
  exact recursive_rate_cap hm
    (mul_nonneg (Nat.cast_nonneg N) (NNN12.alphabet_log_pos (q := q)).le)
    (hbase.trans (moment_capacity N A D)) hε hV

/-- Uniformly raising all affine prices gives a strict supersolution margin:
the recursive part consumes at most 9/13 of the uniform increase. -/
lemma uniform_lift_gap {p M H P B δ V : ℝ} (hmass : M ≤ p * (9 / 4))
    (hδ : 0 ≤ δ) (hV : 0 ≤ V) (hsuper : H + B ≤ (p + M) * P) :
    H + (B + M * δ * V) ≤ (p + M) * (P + gamma * δ * V) := by
  have hh := combined_error_payment hmass hδ hV
  nlinarith only [hh, hsuper]

open CoordinateTensor OM.NNN.Raw
open NNN12 (Shape DyadicTensor volume excess Improves)

/-- The existing all-shape supremum closes the recursion as soon as the
new finite networks and analytic certificate establish `Improves`. -/
theorem invariant_of_combined_step (φ : PolMul.Spectral ℂ) {F : Shape → ℝ}
    (hF : ∀ x, 0 ≤ F x) (step : Improves φ F gamma)
    (x : Shape) (T : DyadicTensor x) : value φ T ≤ (2 : ℝ) ^ F x :=
  NNN12.invariant_of_improves φ hF gamma_bounds.1 gamma_bounds.2 step x T

end OM.NNN13
