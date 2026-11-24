import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Field.GeomSum

/-! # Partition numbers against multiplicity vectors

`pn n` is the number of partitions of `n`.  A multiplicity vector `g : Fin K → Fin (C+1)` lists
how often each part `1, …, K` occurs (at most `C` times); its weight is `∑ k, (k+1) g k`.  Partitions
of `n ≤ N` inject into the vectors with `K = C = N` and weight `n`, and vectors of weight `n` inject
into partitions of `n`.  With `∏_k ∑_c x^((k+1)c) = ∑_g x^(wt g)` this gives the two generating
function inequalities used for the growth of `pn`. -/

namespace OM.NNN30.Partition

open Finset

/-- The partition number `p(n)`. -/
abbrev pn (n : ℕ) : ℕ := Fintype.card n.Partition

/-- Weight of a multiplicity vector. -/
def wt {K C : ℕ} (g : Fin K → Fin (C + 1)) : ℕ := ∑ k : Fin K, ((k : ℕ) + 1) * (g k : ℕ)

lemma wt_le {K C : ℕ} (g : Fin K → Fin (C + 1)) : wt g ≤ K * K * C := by
  unfold wt
  calc ∑ k : Fin K, ((k : ℕ) + 1) * (g k : ℕ) ≤ ∑ _k : Fin K, K * C := by
        apply Finset.sum_le_sum
        intro k _
        exact Nat.mul_le_mul (by omega) (Nat.lt_succ_iff.mp (g k).2)
    _ = K * K * C := by simp [Finset.sum_const, mul_assoc]

/-! ## Partitions to vectors -/

lemma card_parts_le {n : ℕ} (q : n.Partition) : Multiset.card q.parts ≤ n := by
  have h := Multiset.card_nsmul_le_sum (s := q.parts) (a := 1) (fun x hx => q.parts_pos hx)
  simpa [q.parts_sum] using h

lemma count_le {n : ℕ} (q : n.Partition) (m : ℕ) : q.parts.count m ≤ n :=
  (Multiset.count_le_card m q.parts).trans (card_parts_le q)

/-- The multiplicity vector of a partition of `n ≤ N`. -/
def toVec {n N : ℕ} (hn : n ≤ N) (q : n.Partition) : Fin N → Fin (N + 1) :=
  fun k => ⟨q.parts.count ((k : ℕ) + 1), Nat.lt_succ_of_le ((count_le q _).trans hn)⟩

lemma sum_parts_eq {n N : ℕ} (hn : n ≤ N) (q : n.Partition) :
    ∑ k : Fin N, ((k : ℕ) + 1) * q.parts.count ((k : ℕ) + 1) = n := by
  have hsub : q.parts.toFinset ⊆ Finset.range (N + 1) := by
    intro m hm
    rw [Multiset.mem_toFinset] at hm
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le ((Nat.Partition.le_of_mem_parts hm).trans hn))
  have h1 : q.parts.sum = ∑ m ∈ Finset.range (N + 1), q.parts.count m * m := by
    rw [Finset.sum_multiset_count]
    simp only [smul_eq_mul]
    apply Finset.sum_subset hsub
    intro m _ hm
    rw [Multiset.mem_toFinset] at hm
    simp [Multiset.count_eq_zero.mpr hm]
  rw [Finset.sum_range_succ'] at h1
  simp only [mul_zero, add_zero] at h1
  rw [Fin.sum_univ_eq_sum_range (fun k => (k + 1) * q.parts.count (k + 1)) N]
  have h2 := q.parts_sum
  rw [h1] at h2
  calc ∑ i ∈ Finset.range N, (i + 1) * q.parts.count (i + 1)
        = ∑ k ∈ Finset.range N, q.parts.count (k + 1) * (k + 1) :=
          Finset.sum_congr rfl (fun k _ => by ring)
    _ = n := h2

lemma wt_toVec {n N : ℕ} (hn : n ≤ N) (q : n.Partition) : wt (toVec hn q) = n := by
  unfold wt toVec
  simpa using sum_parts_eq hn q

lemma toVec_injective {n N : ℕ} (hn : n ≤ N) : Function.Injective (toVec hn) := by
  intro q q' h
  apply Nat.Partition.ext
  apply Multiset.ext.mpr
  intro m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have h0 : ∀ r : n.Partition, r.parts.count 0 = 0 := fun r =>
      Multiset.count_eq_zero.mpr (fun h0 => (lt_irrefl 0) (r.parts_pos h0))
    rw [h0, h0]
  · by_cases hmN : m ≤ N
    · have hk : m - 1 < N := by omega
      have := congrFun h ⟨m - 1, hk⟩
      simp only [toVec, Fin.mk.injEq] at this
      have hm1 : m - 1 + 1 = m := by omega
      rwa [hm1] at this
    · have hout : ∀ r : n.Partition, r.parts.count m = 0 := fun r =>
        Multiset.count_eq_zero.mpr (fun hmem => hmN ((Nat.Partition.le_of_mem_parts hmem).trans hn))
      rw [hout, hout]

lemma pn_le_card_vec {n N : ℕ} (hn : n ≤ N) :
    pn n ≤ Fintype.card {g : Fin N → Fin (N + 1) // wt g = n} :=
  Fintype.card_le_of_injective (fun q => ⟨toVec hn q, wt_toVec hn q⟩)
    (fun _ _ h => toVec_injective hn (congrArg Subtype.val h))

/-! ## Vectors to partitions -/

/-- The multiset of parts of a multiplicity vector. -/
def ofVecParts {K C : ℕ} (g : Fin K → Fin (C + 1)) : Multiset ℕ :=
  ∑ k : Fin K, Multiset.replicate (g k : ℕ) ((k : ℕ) + 1)

lemma count_ofVecParts {K C : ℕ} (g : Fin K → Fin (C + 1)) (j : Fin K) :
    (ofVecParts g).count ((j : ℕ) + 1) = g j := by
  unfold ofVecParts
  rw [Multiset.count_sum']
  simp only [Multiset.count_replicate]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    have : (k : ℕ) ≠ (j : ℕ) := fun h => hkj (Fin.ext h)
    simp [this]
  · simp

lemma sum_ofVecParts {K C : ℕ} (g : Fin K → Fin (C + 1)) : (ofVecParts g).sum = wt g := by
  unfold ofVecParts wt
  rw [Multiset.sum_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Multiset.sum_replicate, smul_eq_mul, mul_comm]

lemma pos_ofVecParts {K C : ℕ} (g : Fin K → Fin (C + 1)) {i : ℕ} (hi : i ∈ ofVecParts g) :
    0 < i := by
  unfold ofVecParts at hi
  rw [Multiset.mem_sum] at hi
  obtain ⟨k, _, hk⟩ := hi
  rw [(Multiset.eq_of_mem_replicate hk)]
  omega

lemma card_vec_le_pn {K C n : ℕ} :
    Fintype.card {g : Fin K → Fin (C + 1) // wt g = n} ≤ pn n := by
  refine Fintype.card_le_of_injective
    (fun g => (⟨ofVecParts g.1, fun hi => pos_ofVecParts g.1 hi,
      (sum_ofVecParts g.1).trans g.2⟩ : n.Partition)) ?_
  intro g g' h
  apply Subtype.ext
  funext j
  apply Fin.ext
  have h' := congrArg (fun r : n.Partition => r.parts.count ((j : ℕ) + 1)) h
  simpa [count_ofVecParts] using h'

/-! ## Generating function inequalities -/

lemma prod_geom_eq (x : ℝ) (K C : ℕ) :
    ∏ k : Fin K, ∑ c : Fin (C + 1), x ^ (((k : ℕ) + 1) * (c : ℕ)) =
      ∑ g : Fin K → Fin (C + 1), x ^ wt g := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  apply Finset.sum_congr rfl
  intro g _
  rw [Finset.prod_pow_eq_pow_sum]
  rfl

lemma sum_vec_eq (x : ℝ) (K C W : ℕ) (hW : K * K * C ≤ W) :
    ∑ g : Fin K → Fin (C + 1), x ^ wt g =
      ∑ n ∈ Finset.range (W + 1),
        (Fintype.card {g : Fin K → Fin (C + 1) // wt g = n} : ℝ) * x ^ n := by
  rw [← Finset.sum_fiberwise_of_maps_to' (s := Finset.univ) (t := Finset.range (W + 1))
      (g := wt) (fun g _ => Finset.mem_range.mpr (Nat.lt_succ_of_le ((wt_le g).trans hW)))
      (fun n => x ^ n)]
  apply Finset.sum_congr rfl
  intro n _
  rw [Fintype.card_subtype, Finset.sum_const, nsmul_eq_mul]

/-- Partitions of weight at most `N` against the truncated product (upper bound). -/
lemma sum_pn_le_prod {x : ℝ} (hx : 0 ≤ x) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), (pn n : ℝ) * x ^ n ≤
      ∏ k : Fin N, ∑ c : Fin (N + 1), x ^ (((k : ℕ) + 1) * (c : ℕ)) := by
  rw [prod_geom_eq, sum_vec_eq x N N (N * N * N) le_rfl]
  have hsub : Finset.range (N + 1) ⊆ Finset.range (N * N * N + 1) := by
    apply Finset.range_subset_range.mpr
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp
    · have : N ≤ N * N * N := by
        calc N = 1 * 1 * N := by ring
          _ ≤ N * N * N := Nat.mul_le_mul (Nat.mul_le_mul h h) le_rfl
      omega
  calc ∑ n ∈ Finset.range (N + 1), (pn n : ℝ) * x ^ n
      ≤ ∑ n ∈ Finset.range (N + 1),
          (Fintype.card {g : Fin N → Fin (N + 1) // wt g = n} : ℝ) * x ^ n := by
        apply Finset.sum_le_sum
        intro n hn
        have hnN : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast pn_le_card_vec hnN) (pow_nonneg hx n)
    _ ≤ ∑ n ∈ Finset.range (N * N * N + 1),
          (Fintype.card {g : Fin N → Fin (N + 1) // wt g = n} : ℝ) * x ^ n := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro n _ _
        exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx n)

/-- The truncated product against partitions (lower bound). -/
lemma prod_le_sum_pn {x : ℝ} (hx : 0 ≤ x) (K C : ℕ) :
    ∏ k : Fin K, ∑ c : Fin (C + 1), x ^ (((k : ℕ) + 1) * (c : ℕ)) ≤
      ∑ n ∈ Finset.range (K * K * C + 1), (pn n : ℝ) * x ^ n := by
  rw [prod_geom_eq, sum_vec_eq x K C (K * K * C) le_rfl]
  apply Finset.sum_le_sum
  intro n _
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_vec_le_pn) (pow_nonneg hx n)

/-- Monotonicity of `p`: adding a part `1`. -/
lemma pn_mono (n : ℕ) : pn n ≤ pn (n + 1) := by
  refine Fintype.card_le_of_injective
    (fun q => (⟨1 ::ₘ q.parts, fun hi => ?_, by simp [q.parts_sum, add_comm]⟩ : (n + 1).Partition)) ?_
  · rw [Multiset.mem_cons] at hi
    rcases hi with rfl | hi
    · exact Nat.one_pos
    · exact q.parts_pos hi
  · intro q q' h
    apply Nat.Partition.ext
    have := congrArg Nat.Partition.parts h
    simpa using this

lemma pn_monotone : Monotone pn := monotone_nat_of_le_succ pn_mono

lemma one_le_pn (n : ℕ) : 1 ≤ pn n := Fintype.card_pos

end OM.NNN30.Partition
