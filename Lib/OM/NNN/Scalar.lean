import Mathlib

/-!
Exact partition arithmetic for P7, Sections 5--6.

For `7 ≤ n < 110` a balanced partition into about `n/11` blocks suffices.
For `n ≥ 110` use blocks of sizes 11 and 12. All finite comparisons below
are integer comparisons checked by the kernel. The rational radical bounds
are connected to real powers by `gainNumerator_le`.
-/

namespace OM.NNN

open scoped BigOperators

noncomputable def blockGain (a : ℕ) : ℝ :=
  ((a - 1 : ℕ) : ℝ) ^ ((3 : ℝ) / 4) - 1

noncomputable def partitionGain (p : List ℕ) : ℝ := (p.map blockGain).sum

/-- A lower bound on the gain, in millionths. -/
def gainNumerator : ℕ → ℕ
  | 7 => 2833658
  | 8 => 3303517
  | 9 => 3756828
  | 10 => 4196152
  | 11 => 4623413
  | 12 => 5040105
  | 13 => 5447419
  | 14 => 5846325
  | 15 => 6237624
  | 16 => 6621991
  | _ => 0

private theorem gainNumerator_certificate :
    ∀ a : Fin 17, 7 ≤ a.val →
      (gainNumerator a.val + 1000000) ^ 4 ≤
        (a.val - 1) ^ 3 * 1000000 ^ 4 := by
  decide +kernel

lemma rpow_three_quarters_pow_four {x : ℝ} (hx : 0 ≤ x) :
    (x ^ ((3 : ℝ) / 4)) ^ (4 : ℕ) = x ^ (3 : ℕ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

theorem gainNumerator_le (a : ℕ) (ha : 7 ≤ a ∧ a ≤ 16) :
    (gainNumerator a : ℝ) / 1000000 ≤ blockGain a := by
  have hc := gainNumerator_certificate ⟨a, by omega⟩ ha.1
  have hcR : ((gainNumerator a : ℝ) + 1000000) ^ 4 ≤
      ((a - 1 : ℕ) : ℝ) ^ 3 * (1000000 : ℝ) ^ 4 := by
    exact_mod_cast hc
  have hp : (((gainNumerator a : ℝ) + 1000000) / 1000000) ^ 4 ≤
      (((a - 1 : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) ^ (4 : ℕ) := by
    rw [rpow_three_quarters_pow_four (Nat.cast_nonneg _), div_pow]
    exact (div_le_iff₀ (by norm_num)).2 hcR
  have h := le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _) hp
  unfold blockGain
  linarith

theorem sum_gainNumerator_le (p : List ℕ)
    (hp : ∀ a ∈ p, 7 ≤ a ∧ a ≤ 16) :
    ((p.map gainNumerator).sum : ℝ) / 1000000 ≤ partitionGain p := by
  induction p with
  | nil => simp [partitionGain]
  | cons a p ih =>
    have ha := gainNumerator_le a (hp a (by simp))
    have ht := ih (fun b hb => hp b (by simp [hb]))
    simp only [List.map_cons, List.sum_cons, Nat.cast_add]
    unfold partitionGain at *
    simp only [List.map_cons, List.sum_cons]
    linarith

def balancedPartition (n : ℕ) : List ℕ :=
  let k := (n + 5) / 11
  let a := n / k
  let r := n % k
  List.replicate (k - r) a ++ List.replicate r (a + 1)

set_option maxRecDepth 100000 in
private theorem small_partition_certificate :
    ∀ n : Fin 110, 7 ≤ n.val →
      (balancedPartition n.val).sum = n.val ∧
      (∀ a ∈ balancedPartition n.val, 7 ≤ a ∧ a ≤ 16) ∧
      42000000 * n.val ≤
        100 * ((balancedPartition n.val).map gainNumerator).sum +
          441 * Nat.sqrt (n.val * 100000000) := by
  decide +kernel

lemma scaled_nat_sqrt_le (n : ℕ) :
    (Nat.sqrt (n * 100000000) : ℝ) ≤ 10000 * Real.sqrt n := by
  have h := Nat.sqrt_le' (n * 100000000)
  have hR : (Nat.sqrt (n * 100000000) : ℝ) ^ 2 ≤
      (n : ℝ) * 100000000 := by exact_mod_cast h
  have hs := Real.sq_sqrt (Nat.cast_nonneg n)
  have hp := Real.sqrt_nonneg (n : ℝ)
  nlinarith

theorem small_partition_gain (n : ℕ) (hn : 7 ≤ n) (hn' : n < 110) :
    (balancedPartition n).sum = n ∧
    (∀ a ∈ balancedPartition n, 7 ≤ a ∧ a ≤ 16) ∧
    (21 / 50 : ℝ) * n - (441 / 10000 : ℝ) * Real.sqrt n ≤
      partitionGain (balancedPartition n) := by
  obtain ⟨hsum, hb, hnum⟩ := small_partition_certificate ⟨n, hn'⟩ hn
  refine ⟨hsum, hb, ?_⟩
  have hnumR : (42000000 : ℝ) * n ≤
      100 * (((balancedPartition n).map gainNumerator).sum : ℝ) +
        441 * (Nat.sqrt (n * 100000000) : ℝ) := by exact_mod_cast hnum
  have hsqrt := scaled_nat_sqrt_le n
  have hgain := sum_gainNumerator_le (balancedPartition n) hb
  linarith

def largePartition (n : ℕ) : List ℕ :=
  List.replicate (n / 11 - n % 11) 11 ++ List.replicate (n % 11) 12

theorem largePartition_sum (n : ℕ) (hn : 110 ≤ n) :
    (largePartition n).sum = n := by
  have hqr : n % 11 ≤ n / 11 := by omega
  have hdiv := Nat.mod_add_div n 11
  simp [largePartition, List.sum_append, List.sum_replicate, nsmul_eq_mul]
  omega

theorem largePartition_blocks (n : ℕ) :
    ∀ a ∈ largePartition n, a = 11 ∨ a = 12 := by
  intro a ha
  simp only [largePartition, List.mem_append, List.mem_replicate] at ha
  rcases ha with ha | ha
  · exact Or.inl ha.2
  · exact Or.inr ha.2

lemma gain_density (p : List ℕ) (hp : ∀ a ∈ p, a = 11 ∨ a = 12) :
    (21 / 50 : ℝ) * (p.sum : ℝ) ≤ partitionGain p := by
  induction p with
  | nil => simp [partitionGain]
  | cons a p ih =>
    have hblock : (21 / 50 : ℝ) * a ≤ blockGain a := by
      rcases hp a (by simp) with rfl | rfl
      · have h := gainNumerator_le 11 (by omega)
        norm_num [gainNumerator] at h ⊢
        linarith
      · have h := gainNumerator_le 12 (by omega)
        norm_num [gainNumerator] at h ⊢
        linarith
    have ht := ih (fun b hb => hp b (by simp [hb]))
    unfold partitionGain at *
    simp only [List.sum_cons, Nat.cast_add, List.map_cons]
    linarith

/-- The exact arithmetic certificate used in the linear-saving bound. -/
theorem exists_partition_gain (n : ℕ) (hn : 7 ≤ n) :
    ∃ p : List ℕ, p.sum = n ∧ (∀ a ∈ p, 7 ≤ a ∧ a ≤ 16) ∧
      (21 / 50 : ℝ) * n - (441 / 10000 : ℝ) * Real.sqrt n ≤ partitionGain p := by
  by_cases hsmall : n < 110
  · obtain ⟨hs, hb, hg⟩ := small_partition_gain n hn hsmall
    exact ⟨balancedPartition n, hs, hb, hg⟩
  · have hn' : 110 ≤ n := by omega
    refine ⟨largePartition n, largePartition_sum n hn', ?_, ?_⟩
    · intro a ha
      rcases largePartition_blocks n a ha with rfl | rfl <;> constructor <;> omega
    · have h := gain_density (largePartition n) (largePartition_blocks n)
      rw [largePartition_sum n hn'] at h
      have hs := Real.sqrt_nonneg (n : ℝ)
      linarith

/-- The final square-root comparison; no numerical approximation is used. -/
theorem linear_saving_of_square_bound (n : ℕ) (hn : 7 ≤ n) (x G : ℝ)
    (hG : (21 / 50 : ℝ) * n - (441 / 10000 : ℝ) * Real.sqrt n ≤ G)
    (hx : x ^ 2 ≤ (n : ℝ) ^ (3 : ℕ) - G * (n : ℝ) ^ ((3 : ℝ) / 2)) :
    x ≤ (n : ℝ) ^ ((3 : ℝ) / 2) - (21 / 100 : ℝ) * n := by
  have hnR : (7 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hs0 := Real.sqrt_nonneg (n : ℝ)
  have hs2 := Real.sq_sqrt hn0
  have hs1 : 1 ≤ Real.sqrt (n : ℝ) := by nlinarith
  have hpow : (n : ℝ) ^ ((3 : ℝ) / 2) = n * Real.sqrt n := by
    calc
      (n : ℝ) ^ ((3 : ℝ) / 2) = (n : ℝ) ^ (1 + (1 : ℝ) / 2) := by norm_num
      _ = n * Real.sqrt n := by
        rw [Real.rpow_add (by linarith : (0 : ℝ) < n), Real.rpow_one, Real.sqrt_eq_rpow]
  rw [hpow] at hx ⊢
  have hmul := mul_le_mul_of_nonneg_right hG (mul_nonneg hn0 hs0)
  have hsq : ((n : ℝ) * Real.sqrt n - 21 / 100 * n) ^ 2 =
      (n : ℝ) ^ 3 - (21 / 50 * n - 441 / 10000 * Real.sqrt n) *
        ((n : ℝ) * Real.sqrt n) := by
    nlinarith [congrArg (fun z : ℝ => (n : ℝ) ^ 2 * z) hs2,
      congrArg (fun z : ℝ => (n : ℝ) * z) hs2]
  have hx' : x ^ 2 ≤ ((n : ℝ) * Real.sqrt n - 21 / 100 * n) ^ 2 := by
    nlinarith
  have hy : 0 ≤ (n : ℝ) * Real.sqrt n - 21 / 100 * n := by
    nlinarith
  exact le_of_sq_le_sq hx' hy

end OM.NNN
