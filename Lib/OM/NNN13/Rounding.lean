import Lib.OM.NNN13.Moments
import Lib.OM.NNN13.Finite
import Lib.OM.NNN13.Majorants

/-! Uniform bounds for both kinds of rounding. The loss of fewer than two
cycles costs at most ten bits per residual for the four filed alphabets.
Forty-three retained copies pay these losses and all code floors. -/
noncomputable section
open scoped BigOperators
namespace OM.NNN13

variable {q : ℕ} [Fact q.Prime]

lemma alphabet_log_le_five (hq : q ≤ 19) : Real.logb 2 q ≤ 5 := by
  apply (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2)
    (NNN12.alphabet_pos (q := q))).2
  have hq' : (q : ℝ) ≤ 19 := by exact_mod_cast hq
  norm_num
  linarith

lemma momentExponent_mono_slope (N : ℕ) (A : ℝ) {D E : ℝ} (hDE : D ≤ E) :
    NNN12.momentExponent q N A D ≤ NNN12.momentExponent q N A E := by
  have hh := mul_le_mul_of_nonneg_left
    (logMoment_mono (q := q) (d := 1) (by norm_num) hDE) (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  simpa only [logMoment, one_mul, NNN12.momentExponent, add_le_add_iff_left] using! hh

omit [Fact q.Prime] in
lemma momentExponent_add (N : ℕ) (A D E : ℝ) :
    NNN12.momentExponent q N (A + E) D = NNN12.momentExponent q N A D + E := by
  dsimp [NNN12.momentExponent]
  ring

theorem moment_rounded_cycles (hq : q ≤ 19) (N : ℕ) (A E d D : ℝ)
    (hN : (N : ℝ) ≤ E) (hE : E ≤ N + 2) (hd : 0 ≤ d) (hD : D ≤ 0) :
    NNN12.momentExponent q N A (d * D) ≤ A + E * logMoment q d D + 10 := by
  have hc := cycle_rounding_cost (q := q) hN hE hd hD
  have hl := alphabet_log_le_five hq
  change A + N * logMoment q d D ≤ _
  linarith

lemma alphabet_rounding_constant (q : Fin 3 → ℕ) (hq : ∀ i, q i ≤ 19)
    {a : ℕ} (ha : 43 ≤ a) :
    (∏ i, (q i : ℝ)) * (2 : ℝ) ^ (30 : ℝ) + 2 ≤ (2 : ℝ) ^ a := by
  have hp : (∏ i, (q i : ℝ)) ≤ ∏ _i : Fin 3, (19 : ℝ) := by
    apply Finset.prod_le_prod₀
    · intro i _; exact Nat.cast_nonneg _
    · intro i _; exact_mod_cast hq i
  have ha' := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) ha
  norm_num at hp ha' ⊢
  linarith

lemma groupDegrees_le (a b c : ℕ) (i : Fin 3) : groupDegrees a b c i ≤ a + b + c := by
  fin_cases i <;> simp [groupDegrees]

lemma groupIntercepts_add (a b c : ℕ) (C : Fin 3 → Fin 3 → ℝ) (x : Fin 3 → ℝ)
    (ε : ℝ) (i : Fin 3) :
    groupIntercepts a b c (fun i j => C i j + ε) x i =
      groupIntercepts a b c C x i + groupDegrees a b c i * ε * (x 0 + x 1 + x 2) := by
  simp only [groupIntercepts, plane_add_constant]
  ring

lemma groupSlopes_add (d : Fin 3 → ℕ) (t : Fin 3 → ℝ) (C : Fin 3 → Fin 3 → ℝ)
    (ε : ℝ) (i : Fin 3) :
    groupSlopes d t (fun i j => C i j + ε) i = groupSlopes d t C i - 2 * d i * ε := by
  fin_cases i <;> dsimp [groupSlopes] <;> ring

theorem recursive_moment_bound (q N d : Fin 3 → ℕ) [∀ i, Fact (q i).Prime]
    (a b c : ℕ) (t : Fin 3 → ℝ) (C : Fin 3 → Fin 3 → ℝ) (x : Fin 3 → ℝ)
    (B : Fin 3 → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hB : ∀ i, NNN12.momentExponent (q i) (N i)
      (groupIntercepts a b c C x i) (groupSlopes d t C i) ≤ B i) (i : Fin 3) :
    NNN12.momentExponent (q i) (N i)
      (groupIntercepts a b c (fun i j => C i j + ε) x i)
      (groupSlopes d t (fun i j => C i j + ε) i) ≤
      B i + groupDegrees a b c i * ε * (x 0 + x 1 + x 2) := by
  rw [groupIntercepts_add, groupSlopes_add, momentExponent_add]
  apply add_le_add _ le_rfl
  apply (momentExponent_mono_slope (N i) _ ?_).trans (hB i)
  have hh : 0 ≤ 2 * (d i : ℝ) * ε := by positivity
  linarith

end OM.NNN13
