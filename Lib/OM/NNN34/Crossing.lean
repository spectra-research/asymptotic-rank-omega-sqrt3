import Lib.OM.NNN34.JetSums
import Lib.OM.NNN32.Cuts
import PLATFORM.Statements.«R114.11»

/-! # Simultaneous rank bounds for the normalized prefix and suffix -/

namespace OM.NNN34

open OM.NNN30.Crossing P2M.R114 PowerSeries Semicontinuity

theorem cutoff_le (H : ℕ) : cutoff H ≤ H := Nat.findGreatest_le H

theorem cutoff_fits (H : ℕ) : NNN30.Rect.Qn (cutoff H) ≤ (partitionSide H : ℕ) := by
  apply Nat.findGreatest_spec (P := fun j => NNN30.Rect.Qn j ≤ (partitionSide H : ℕ)) (Nat.zero_le H)
  simp only [NNN30.Rect.Qn, zero_add, Finset.sum_range_one, Fintype.card_unique]
  exact (partitionSide H).pos

private noncomputable def farEnd (H : ℕ) (β : Pt × ℕ → Pt × ℕ → ℂ⟦X⟧) (m : ℕ) (t : m.Partition)
    (q : H.Partition × H.Partition) : ℂ :=
  farVal β t.parts (q.1.parts.map (fun a => (Pt.q, a)) + q.2.parts.map (fun b => (Pt.inf, b)))

private theorem prefix_factor (H k : ℕ) (hk : k ≤ 2 * (H + H)) :
    ∃ L : H.Partition × H.Partition → States k → ℂ, ∀ z x y w,
      ∑ j ∈ Finset.range (k+1), Bp H H j z x y w =
        ∑ s, L (z,x) s * farEnd H ker0 s.1.val s.2 (y,w) := by
  let P := fun (i j : H.Partition × H.Partition) => Ppart H H i.1 i.2 j.1 j.2
  let U := fun (i j : H.Partition × H.Partition) =>
    wickM ker0 (labels4 i.1.parts i.2.parts j.1.parts j.2.parts)
  obtain ⟨L, hL⟩ := weighted_jet_factor 1 (-1) _ k hk (fun _ => 1)
    ((X-1)^(H+H)) P U (farEnd H ker0)
    (fun i j => by
      simpa only [P, U, Ppart, shift1, Nat.Partition.parts_sum] using
        P4_coe (pos_parts i.1) (pos_parts i.2) (pos_parts j.1) (pos_parts j.2))
    (fun i m => by
      obtain ⟨l, hl⟩ := row_fact (pos_parts i.1) (pos_parts i.2) m
      exact ⟨l, fun j => hl _ _ (pos_parts j.1) (pos_parts j.2)⟩)
  refine ⟨L, fun z x y w => ?_⟩
  rw [← Fin.sum_univ_eq_sum_range]
  simpa only [Bp, P, one_mul] using hL (z,x) (y,w)

private theorem suffix_factor (H k : ℕ) (hk : k < 4*H) :
    ∃ L : H.Partition × H.Partition → States (4*H-k-1) → ℂ, ∀ z x y w,
      ∑ j ∈ Finset.Ioc k (4*H), Bp H H j z x y w =
        ∑ s, L (z,y) s * farEnd H ker1 s.1.val s.2 (x,w) := by
  let D := 2*(H+H)
  have hD : D = 4*H := by dsimp [D]; omega
  let K := 4*H-k-1
  let P := fun (i j : H.Partition × H.Partition) => (Ppart H H i.1 j.1 i.2 j.2).comp (Polynomial.X+1)
  let U := fun (i j : H.Partition × H.Partition) =>
    wickM ker1 (labels4 i.1.parts i.2.parts j.1.parts j.2.parts)
  obtain ⟨L, hL⟩ := weighted_jet_factor (-1) (-1) D K (by dsimp [K]; omega)
    (fun h => (-1)^(D-h.val)) ((1+X)^(H+H)) P U (farEnd H ker1)
    (fun i j => by
      simpa only [P, U, Ppart, shift1, Nat.Partition.parts_sum] using
        P4_shift1 (pos_parts i.1) (pos_parts j.1) (pos_parts i.2) (pos_parts j.2))
    (fun i m => by
      obtain ⟨l, hl⟩ := col_fact (pos_parts i.1) (pos_parts i.2) m
      exact ⟨l, fun j => hl _ _ (pos_parts j.1) (pos_parts j.2)⟩)
  refine ⟨L, fun z x y w => ?_⟩
  rw [← hL (z,y) (x,w)]
  rw [Fin.sum_univ_eq_sum_range (fun h =>
    (-1 : ℂ)^(D-h) * (trL (-1) (-1) D (P (z,y) (x,w))).coeff h)]
  apply Finset.sum_nbij' (fun j => D-j) (fun h => D-h)
  · simp only [Finset.mem_Ioc, Finset.mem_range, K]; omega
  · simp only [Finset.mem_Ioc, Finset.mem_range, K]; omega
  · simp only [Finset.mem_Ioc]; omega
  · simp only [Finset.mem_range, K]; omega
  · intro j hj
    obtain ⟨_, hj'⟩ := Finset.mem_Ioc.mp hj
    have he : D-(D-j) = j := by omega
    rw [he]
    exact basis_coeff_at_one _ _ (Ppart_natDegree H H z x y w) j (by omega)

private theorem normalized_sum (H : ℕ) (s : Finset ℕ) (z x y w : H.Partition) :
    ∑ j ∈ s, Bfin H H j z x y w = ∑ y', ∑ w', (∑ j ∈ s, Bp H H j z x y' w') *
      (Gmat H)⁻¹ y' y * Dinv H w' w := by
  simp only [Bfin, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

private theorem rotate {I J S : Type} [Fintype I] [Fintype J] [Fintype S] (f : I → J → S → ℂ) :
    ∑ i, ∑ j, ∑ s, f i j s = ∑ s, ∑ i, ∑ j, f i j s := by
  simp_rw [Finset.sum_comm (f := fun j s => f _ j s)]
  exact Finset.sum_comm

theorem proof_R114_11 : S_R114_11 := by
  classical
  intro H hH
  let D := partitionSide H
  let k := cutoff H
  let e := partitionAt H
  let S : NNN32.Four D := fun a => ∑ j ∈ Finset.Ioc k (4*H),
    Bfin H H j (e (a 0)) (e (a 1)) (e (a 2)) (e (a 3))
  have hk : k ≤ H := cutoff_le H
  refine ⟨?_, ?_, cutoff_fits H, ?_⟩
  · funext a
    let f := fun j => Bfin H H j (e (a 0)) (e (a 1)) (e (a 2)) (e (a 3))
    change (∑ j ∈ Finset.range (k+1), f j) + (∑ j ∈ Finset.Ioc k (4*H), f j) = _
    rw [← Finset.sum_union (by
      apply Finset.disjoint_left.mpr
      simp only [Finset.mem_range, Finset.mem_Ioc]; omega)]
    have hu : Finset.range (k+1) ∪ Finset.Ioc k (4*H) = Finset.range (2*(H+H)+1) := by
      ext j
      simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ioc]; omega
    rw [hu]
    dsimp only [f]
    rw [Bfin_sum]
    simp [P2M.R113.matching, e]
  · obtain ⟨L, hL⟩ := prefix_factor H k (by omega)
    rw [← NNN32.rowMatrix_rank, NNN30.Rect.Qn, ← card_sigma_partition]
    apply rank_le_of_factor _ (fun i s => L (e i.1,e i.2) s) (fun s j => ∑ y', ∑ w',
      farEnd H ker0 s.1.val s.2 (y',w') * (Gmat H)⁻¹ y' (e j.1) * Dinv H w' (e j.2))
    intro i j
    change (∑ j' ∈ Finset.range (k+1), Bfin H H j' (e i.1) (e i.2) (e j.1) (e j.2)) = _
    rw [normalized_sum]
    simp only [hL, Finset.sum_mul, Finset.mul_sum]
    rw [rotate (fun y' w' s => L (e i.1,e i.2) s * farEnd H ker0 s.1.val s.2 (y',w') *
      (Gmat H)⁻¹ y' (e j.1) * Dinv H w' (e j.2))]
    simp [mul_assoc]
  · change flatRank S {0,2} ≤ NNN30.Rect.Qn (4*H-k-1)
    obtain ⟨L, hL⟩ := suffix_factor H k (by omega)
    rw [← NNN32.colMatrix_rank, NNN30.Rect.Qn, ← card_sigma_partition]
    apply rank_le_of_factor _ (fun i s => ∑ y', L (e i.1,y') s * (Gmat H)⁻¹ y' (e i.2))
      (fun s j => ∑ w', farEnd H ker1 s.1.val s.2 (e j.1,w') * Dinv H w' (e j.2))
    intro i j
    change (∑ j' ∈ Finset.Ioc k (4*H), Bfin H H j' (e i.1) (e j.1) (e i.2) (e j.2)) = _
    rw [normalized_sum]
    simp only [hL, Finset.sum_mul]
    rw [rotate (fun y' w' s => L (e i.1,y') s * farEnd H ker1 s.1.val s.2 (e j.1,w') *
      (Gmat H)⁻¹ y' (e i.2) * Dinv H w' (e j.2))]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro s _
    apply Finset.sum_congr rfl; intro y' _
    apply Finset.sum_congr rfl; intro w' _
    ring

end OM.NNN34

