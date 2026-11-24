import Lib.OM.NNN11.Telescope

/-! The other two heavy-party telescope orders, with finite lists and values. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN11.Network
open CoordinateTensor OM.NNN.Raw OM.NNN2
set_option maxHeartbeats 1000000

variable {A B C X Y Z : Type}
  [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C]
  [Fintype X] [Fintype Y] [Fintype Z]

theorem telescope_sum_lastBC {I J K : Type} (T : Tensor ℂ X Y Z)
    (s : Finset I) (t : Finset J) (u : Finset K)
    (P : I → Operator (BondAB A B X Y)) (Q : J → Operator (BondBC B C Y Z))
    (R : K → Operator (BondCA C A Z X)) :
    contract (A := A) (B := B) (C := C) T (identity _ + ∑ i ∈ s, P i) (identity _ + ∑ j ∈ t, Q j) (identity _ + ∑ k ∈ u, R k) =
      contract (A := A) (B := B) (C := C) T (identity _) (identity _) (identity _) +
        (∑ j ∈ t, contract (A := A) (B := B) (C := C) T (identity _) (Q j) (identity _)) +
        (∑ i ∈ s, contract (A := A) (B := B) (C := C) T (P i) (identity _ + ∑ j ∈ t, Q j) (identity _)) +
        (∑ k ∈ u, contract (A := A) (B := B) (C := C) T (identity _ + ∑ i ∈ s, P i) (identity _ + ∑ j ∈ t, Q j) (R k)) := by
  rw [telescope_lastBC]
  have hP := map_sum (linearAB (A := A) (B := B) (C := C) T (identity _ + ∑ j ∈ t, Q j) (identity _)) P s
  change contract (A := A) (B := B) (C := C) T (∑ i ∈ s, P i) (identity _ + ∑ j ∈ t, Q j) (identity _) = _ at hP
  have hQ := map_sum (linearBC (A := A) (B := B) (C := C) T (identity _) (identity _)) Q t
  change contract (A := A) (B := B) (C := C) T (identity _) (∑ j ∈ t, Q j) (identity _) = _ at hQ
  have hR := map_sum (linearCA (A := A) (B := B) (C := C) T (identity _ + ∑ i ∈ s, P i) (identity _ + ∑ j ∈ t, Q j)) R u
  change contract (A := A) (B := B) (C := C) T (identity _ + ∑ i ∈ s, P i) (identity _ + ∑ j ∈ t, Q j) (∑ k ∈ u, R k) = _ at hR
  rw [hP, hQ, hR]
  rfl

theorem telescoped_value_lastBC {I J K : Type} (φ : PolMul.Spectral ℂ)
    (T : Tensor ℂ X Y Z)
    (s : Finset I) (t : Finset J) (u : Finset K)
    (P : I → Operator (BondAB A B X Y)) (Q : J → Operator (BondBC B C Y Z))
    (R : K → Operator (BondCA C A Z X))
    (a : I → ℝ) (b : J → ℝ) (c : K → ℝ)
    (ha : ∀ i ∈ s, value φ (contract (A := A) (B := B) (C := C) T (P i) (identity _ + ∑ j ∈ t, Q j) (identity _)) ≤ a i)
    (hb : ∀ j ∈ t, value φ (contract (A := A) (B := B) (C := C) T (identity _) (Q j) (identity _)) ≤ b j)
    (hc : ∀ k ∈ u, value φ (contract (A := A) (B := B) (C := C) T (identity _ + ∑ i ∈ s, P i) (identity _ + ∑ j ∈ t, Q j) (R k)) ≤ c k) :
    value φ (contract (A := A) (B := B) (C := C) T (identity _) (identity _) (identity _)) ≤
      value φ (contract (A := A) (B := B) (C := C) T (identity _ + ∑ i ∈ s, P i) (identity _ + ∑ j ∈ t, Q j) (identity _ + ∑ k ∈ u, R k)) +
        (∑ i ∈ s, a i) + (∑ j ∈ t, b j) + ∑ k ∈ u, c k := by
  have h0 := remove_sum_bound φ t (fun j => contract (A := A) (B := B) (C := C) T (identity _) (Q j) (identity _)) b hb
    (contract (A := A) (B := B) (C := C) T (identity _) (identity _) (identity _))
  have h1 := remove_sum_bound φ s (fun i => contract (A := A) (B := B) (C := C) T (P i) (identity _ + ∑ j ∈ t, Q j) (identity _)) a ha
    (contract (A := A) (B := B) (C := C) T (identity _) (identity _) (identity _) + (∑ j ∈ t, contract (A := A) (B := B) (C := C) T (identity _) (Q j) (identity _)))
  have h2 := remove_sum_bound φ u (fun k => contract (A := A) (B := B) (C := C) T (identity _ + ∑ i ∈ s, P i) (identity _ + ∑ j ∈ t, Q j) (R k)) c hc
    (contract (A := A) (B := B) (C := C) T (identity _) (identity _) (identity _) + (∑ j ∈ t, contract (A := A) (B := B) (C := C) T (identity _) (Q j) (identity _)) + (∑ i ∈ s, contract (A := A) (B := B) (C := C) T (P i) (identity _ + ∑ j ∈ t, Q j) (identity _)))
  rw [← telescope_sum_lastBC] at h2
  linarith

theorem telescope_sum_lastCA {I J K : Type} (T : Tensor ℂ X Y Z)
    (s : Finset I) (t : Finset J) (u : Finset K)
    (P : I → Operator (BondAB A B X Y)) (Q : J → Operator (BondBC B C Y Z))
    (R : K → Operator (BondCA C A Z X)) :
    contract (A := A) (B := B) (C := C) T (identity _ + ∑ i ∈ s, P i) (identity _ + ∑ j ∈ t, Q j) (identity _ + ∑ k ∈ u, R k) =
      contract (A := A) (B := B) (C := C) T (identity _) (identity _) (identity _) +
        (∑ k ∈ u, contract (A := A) (B := B) (C := C) T (identity _) (identity _) (R k)) +
        (∑ j ∈ t, contract (A := A) (B := B) (C := C) T (identity _) (Q j) (identity _ + ∑ k ∈ u, R k)) +
        (∑ i ∈ s, contract (A := A) (B := B) (C := C) T (P i) (identity _ + ∑ j ∈ t, Q j) (identity _ + ∑ k ∈ u, R k)) := by
  rw [telescope_lastCA]
  have hP := map_sum (linearAB (A := A) (B := B) (C := C) T (identity _ + ∑ j ∈ t, Q j) (identity _ + ∑ k ∈ u, R k)) P s
  change contract (A := A) (B := B) (C := C) T (∑ i ∈ s, P i) (identity _ + ∑ j ∈ t, Q j) (identity _ + ∑ k ∈ u, R k) = _ at hP
  have hQ := map_sum (linearBC (A := A) (B := B) (C := C) T (identity _) (identity _ + ∑ k ∈ u, R k)) Q t
  change contract (A := A) (B := B) (C := C) T (identity _) (∑ j ∈ t, Q j) (identity _ + ∑ k ∈ u, R k) = _ at hQ
  have hR := map_sum (linearCA (A := A) (B := B) (C := C) T (identity _) (identity _)) R u
  change contract (A := A) (B := B) (C := C) T (identity _) (identity _) (∑ k ∈ u, R k) = _ at hR
  rw [hP, hQ, hR]
  rfl

theorem telescoped_value_lastCA {I J K : Type} (φ : PolMul.Spectral ℂ)
    (T : Tensor ℂ X Y Z)
    (s : Finset I) (t : Finset J) (u : Finset K)
    (P : I → Operator (BondAB A B X Y)) (Q : J → Operator (BondBC B C Y Z))
    (R : K → Operator (BondCA C A Z X))
    (a : I → ℝ) (b : J → ℝ) (c : K → ℝ)
    (ha : ∀ i ∈ s, value φ (contract (A := A) (B := B) (C := C) T (P i) (identity _ + ∑ j ∈ t, Q j) (identity _ + ∑ k ∈ u, R k)) ≤ a i)
    (hb : ∀ j ∈ t, value φ (contract (A := A) (B := B) (C := C) T (identity _) (Q j) (identity _ + ∑ k ∈ u, R k)) ≤ b j)
    (hc : ∀ k ∈ u, value φ (contract (A := A) (B := B) (C := C) T (identity _) (identity _) (R k)) ≤ c k) :
    value φ (contract (A := A) (B := B) (C := C) T (identity _) (identity _) (identity _)) ≤
      value φ (contract (A := A) (B := B) (C := C) T (identity _ + ∑ i ∈ s, P i) (identity _ + ∑ j ∈ t, Q j) (identity _ + ∑ k ∈ u, R k)) +
        (∑ i ∈ s, a i) + (∑ j ∈ t, b j) + ∑ k ∈ u, c k := by
  have h0 := remove_sum_bound φ u (fun k => contract (A := A) (B := B) (C := C) T (identity _) (identity _) (R k)) c hc
    (contract (A := A) (B := B) (C := C) T (identity _) (identity _) (identity _))
  have h1 := remove_sum_bound φ t (fun j => contract (A := A) (B := B) (C := C) T (identity _) (Q j) (identity _ + ∑ k ∈ u, R k)) b hb
    (contract (A := A) (B := B) (C := C) T (identity _) (identity _) (identity _) + (∑ k ∈ u, contract (A := A) (B := B) (C := C) T (identity _) (identity _) (R k)))
  have h2 := remove_sum_bound φ s (fun i => contract (A := A) (B := B) (C := C) T (P i) (identity _ + ∑ j ∈ t, Q j) (identity _ + ∑ k ∈ u, R k)) a ha
    (contract (A := A) (B := B) (C := C) T (identity _) (identity _) (identity _) + (∑ k ∈ u, contract (A := A) (B := B) (C := C) T (identity _) (identity _) (R k)) + (∑ j ∈ t, contract (A := A) (B := B) (C := C) T (identity _) (Q j) (identity _ + ∑ k ∈ u, R k)))
  rw [← telescope_sum_lastCA] at h2
  linarith

end OM.NNN11.Network
