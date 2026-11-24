import Lib.OM.NNN30.Crossing.Basis
import Lib.OM.NNN30.Crossing.FourPoint

/-! # Rank factorisation from a truncated operator product expansion

A coefficient of the transformed polynomial only sees the first `k + 1` coefficients of the
underlying power series. Multiplication by a fixed dressing series and the change of polynomial
basis therefore use just one copy of the intermediate partition space at each weight. -/

namespace OM.NNN30.Crossing

open PowerSeries

private theorem coeff_mul_cut (A U : ℂ⟦X⟧) {j k : ℕ} (hj : j ≤ k) :
    coeff j (A * U) = ∑ m ∈ Finset.range (k + 1),
      (if m ≤ j then coeff (j - m) A else 0) * coeff m U := by
  rw [mul_comm A U, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun m n => coeff m U * coeff n A)]
  calc
    _ = ∑ m ∈ Finset.range (j + 1),
        (if m ≤ j then coeff (j - m) A else 0) * coeff m U := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [if_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)), mul_comm]
    _ = _ := Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hj)) (by
      intro m _ hm
      rw [if_neg (fun h => hm (Finset.mem_range.mpr (Nat.lt_succ_of_le h))), zero_mul])

/-- The linear functional on the truncated series that extracts the chosen basis coefficient. -/
theorem exists_jet_weights (c d : ℂ) (D k : ℕ) (hk : k ≤ D) (A : ℂ⟦X⟧) :
    ∃ weights : Fin (k + 1) → ℂ, ∀ (P : Polynomial ℂ) (U : ℂ⟦X⟧), (P : ℂ⟦X⟧) = A * U →
      (trL c d D P).coeff k = ∑ m, weights m * coeff m.val U := by
  let b := fun j => (Polynomial.X ^ j *
    (Polynomial.C c * Polynomial.X + Polynomial.C d) ^ (D - j) : Polynomial ℂ).coeff k
  let a := fun j m => if m ≤ j then coeff (j - m) A else 0
  refine ⟨fun m => ∑ j ∈ Finset.range (k + 1), a j m.val * b j, ?_⟩
  intro P U hP
  have hcoeff (j : ℕ) (hj : j ≤ k) :
      P.coeff j = ∑ m ∈ Finset.range (k + 1), a j m * coeff m U := by
    rw [← Polynomial.coeff_coe, hP, coeff_mul_cut A U hj]
  rw [coeff_trL c d D P k hk, Fin.sum_univ_eq_sum_range
    (fun m => (∑ j ∈ Finset.range (k + 1), a j m * b j) * coeff m U)]
  change ∑ j ∈ Finset.range (k + 1), P.coeff j * b j = _
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm (f := fun m j => a j m * b j * coeff m U)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hcoeff j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)), Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m _
  ring

abbrev States (k : ℕ) := Σ m : Fin (k + 1), m.val.Partition

/-- Combining the coefficients at distinct weights factors through their disjoint union. -/
theorem jet_factor {I J : Type} (c d scale : ℂ) (D k : ℕ) (hk : k ≤ D)
    (A : ℂ⟦X⟧) (P : I → J → Polynomial ℂ) (U : I → J → ℂ⟦X⟧)
    (R : (m : ℕ) → m.Partition → J → ℂ)
    (hP : ∀ i j, (P i j : ℂ⟦X⟧) = A * U i j)
    (hU : ∀ i m, ∃ l : m.Partition → ℂ, ∀ j, coeff m (U i j) = ∑ t, l t * R m t j) :
    ∃ L : I → States k → ℂ, ∀ i j, scale * (trL c d D (P i j)).coeff k =
      ∑ s : States k, L i s * R s.1.val s.2 j := by
  classical
  choose l hl using hU
  obtain ⟨weight, hw⟩ := exists_jet_weights c d D k hk A
  refine ⟨fun i s => scale * weight s.1 * l i s.1.val s.2, ?_⟩
  intro i j
  rw [hw _ _ (hP i j), Finset.mul_sum, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro m _
  rw [hl, ← mul_assoc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring

end OM.NNN30.Crossing
