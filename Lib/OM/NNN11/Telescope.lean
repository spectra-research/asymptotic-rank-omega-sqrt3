import Lib.OM.NNN11.Network
import Lib.OM.NNN10.Values

/-! The literal three-list telescope for the rectangular ownership network.
Later bond operators stay inside each earlier correction. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN11.Network
open CoordinateTensor OM.NNN.Raw OM.NNN2
set_option maxHeartbeats 1000000

variable {A B C X Y Z : Type}
  [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C]
  [Fintype X] [Fintype Y] [Fintype Z]

def linearAB (T : Tensor ℂ X Y Z)
    (Q : Operator (BondBC B C Y Z)) (R : Operator (BondCA C A Z X)) :
    Operator (BondAB A B X Y) →ₗ[ℂ]
      Tensor ℂ (Outputs A B C X) (Outputs A B C Y) (Outputs A B C Z) where
  toFun P := contract (A := A) (B := B) (C := C) T P Q R
  map_add' P P' := by
    funext x y z
    simp [contract, add_mul, Finset.sum_add_distrib]
  map_smul' z P := by
    funext x y w
    simp [contract, Finset.mul_sum, mul_assoc]

def linearBC (T : Tensor ℂ X Y Z)
    (P : Operator (BondAB A B X Y)) (R : Operator (BondCA C A Z X)) :
    Operator (BondBC B C Y Z) →ₗ[ℂ]
      Tensor ℂ (Outputs A B C X) (Outputs A B C Y) (Outputs A B C Z) where
  toFun Q := contract (A := A) (B := B) (C := C) T P Q R
  map_add' Q Q' := by
    funext x y z
    simp [contract, add_mul, mul_add, Finset.sum_add_distrib]
  map_smul' z Q := by
    funext x y w
    simp only [contract, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
    repeat' (apply Finset.sum_congr rfl; intro _ _)
    ring

def linearCA (T : Tensor ℂ X Y Z)
    (P : Operator (BondAB A B X Y)) (Q : Operator (BondBC B C Y Z)) :
    Operator (BondCA C A Z X) →ₗ[ℂ]
      Tensor ℂ (Outputs A B C X) (Outputs A B C Y) (Outputs A B C Z) where
  toFun R := contract (A := A) (B := B) (C := C) T P Q R
  map_add' R R' := by
    funext x y z
    simp [contract, add_mul, mul_add, Finset.sum_add_distrib]
  map_smul' z R := by
    funext x y w
    simp only [contract, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
    repeat' (apply Finset.sum_congr rfl; intro _ _)
    ring

lemma contract_add_AB (T : Tensor ℂ X Y Z)
    (P P' : Operator (BondAB A B X Y)) (Q : Operator (BondBC B C Y Z))
    (R : Operator (BondCA C A Z X)) :
    contract (A := A) (B := B) (C := C) T (P + P') Q R = contract (A := A) (B := B) (C := C) T P Q R + contract (A := A) (B := B) (C := C) T P' Q R :=
  (linearAB (A := A) (B := B) (C := C) T Q R).map_add P P'

lemma contract_add_BC (T : Tensor ℂ X Y Z)
    (P : Operator (BondAB A B X Y)) (Q Q' : Operator (BondBC B C Y Z))
    (R : Operator (BondCA C A Z X)) :
    contract (A := A) (B := B) (C := C) T P (Q + Q') R = contract (A := A) (B := B) (C := C) T P Q R + contract (A := A) (B := B) (C := C) T P Q' R :=
  (linearBC (A := A) (B := B) (C := C) T P R).map_add Q Q'

lemma contract_add_CA (T : Tensor ℂ X Y Z)
    (P : Operator (BondAB A B X Y)) (Q : Operator (BondBC B C Y Z))
    (R R' : Operator (BondCA C A Z X)) :
    contract (A := A) (B := B) (C := C) T P Q (R + R') = contract (A := A) (B := B) (C := C) T P Q R + contract (A := A) (B := B) (C := C) T P Q R' :=
  (linearCA (A := A) (B := B) (C := C) T P Q).map_add R R'

/-- BC first, CA second, AB last: the last list retains all C-owned copies. -/
theorem telescope (T : Tensor ℂ X Y Z)
    (P : Operator (BondAB A B X Y)) (Q : Operator (BondBC B C Y Z))
    (R : Operator (BondCA C A Z X)) :
    contract (A := A) (B := B) (C := C) T (identity _ + P) (identity _ + Q) (identity _ + R) =
      contract (A := A) (B := B) (C := C) T (identity _) (identity _) (identity _) +
        contract (A := A) (B := B) (C := C) T P (identity _) (identity _) +
        contract (A := A) (B := B) (C := C) T (identity _ + P) (identity _) R +
        contract (A := A) (B := B) (C := C) T (identity _ + P) Q (identity _ + R) := by
  rw [contract_add_BC, contract_add_CA, contract_add_AB]

/-- CA first, AB second, BC last. -/
theorem telescope_lastBC (T : Tensor ℂ X Y Z)
    (P : Operator (BondAB A B X Y)) (Q : Operator (BondBC B C Y Z))
    (R : Operator (BondCA C A Z X)) :
    contract (A := A) (B := B) (C := C) T (identity _ + P) (identity _ + Q) (identity _ + R) =
      contract (A := A) (B := B) (C := C) T (identity _) (identity _) (identity _) +
        contract (A := A) (B := B) (C := C) T (identity _) Q (identity _) +
        contract (A := A) (B := B) (C := C) T P (identity _ + Q) (identity _) +
        contract (A := A) (B := B) (C := C) T (identity _ + P) (identity _ + Q) R := by
  rw [contract_add_CA, contract_add_AB, contract_add_BC]

/-- AB first, BC second, CA last. -/
theorem telescope_lastCA (T : Tensor ℂ X Y Z)
    (P : Operator (BondAB A B X Y)) (Q : Operator (BondBC B C Y Z))
    (R : Operator (BondCA C A Z X)) :
    contract (A := A) (B := B) (C := C) T (identity _ + P) (identity _ + Q) (identity _ + R) =
      contract (A := A) (B := B) (C := C) T (identity _) (identity _) (identity _) +
        contract (A := A) (B := B) (C := C) T (identity _) (identity _) R +
        contract (A := A) (B := B) (C := C) T (identity _) Q (identity _ + R) +
        contract (A := A) (B := B) (C := C) T P (identity _ + Q) (identity _ + R) := by
  rw [contract_add_AB, contract_add_BC, contract_add_CA]

theorem telescope_sum {I J K : Type} (T : Tensor ℂ X Y Z)
    (s : Finset I) (t : Finset J) (u : Finset K)
    (P : I → Operator (BondAB A B X Y)) (Q : J → Operator (BondBC B C Y Z))
    (R : K → Operator (BondCA C A Z X)) :
    contract (A := A) (B := B) (C := C) T (identity _ + ∑ i ∈ s, P i) (identity _ + ∑ j ∈ t, Q j)
      (identity _ + ∑ k ∈ u, R k) =
      contract (A := A) (B := B) (C := C) T (identity _) (identity _) (identity _) +
        (∑ i ∈ s, contract (A := A) (B := B) (C := C) T (P i) (identity _) (identity _)) +
        (∑ k ∈ u, contract (A := A) (B := B) (C := C) T (identity _ + ∑ i ∈ s, P i) (identity _) (R k)) +
        ∑ j ∈ t, contract (A := A) (B := B) (C := C) T (identity _ + ∑ i ∈ s, P i)
          (Q j) (identity _ + ∑ k ∈ u, R k) := by
  rw [telescope]
  have hP := map_sum (linearAB (A := A) (B := B) (C := C) T (identity _) (identity _)) P s
  have hR := map_sum (linearCA (A := A) (B := B) (C := C) T (identity _ + ∑ i ∈ s, P i) (identity _)) R u
  have hQ := map_sum (linearBC (A := A) (B := B) (C := C) T (identity _ + ∑ i ∈ s, P i)
    (identity _ + ∑ k ∈ u, R k)) Q t
  change contract (A := A) (B := B) (C := C) T (∑ i ∈ s, P i) (identity _) (identity _) = _ at hP
  change contract (A := A) (B := B) (C := C) T (identity _ + ∑ i ∈ s, P i) (identity _) (∑ k ∈ u, R k) = _ at hR
  change contract (A := A) (B := B) (C := C) T (identity _ + ∑ i ∈ s, P i) (∑ j ∈ t, Q j)
    (identity _ + ∑ k ∈ u, R k) = _ at hQ
  rw [hP, hR, hQ]
  rfl

lemma remove_sum_bound {I E F G : Type} [Fintype E] [Fintype F] [Fintype G]
    (φ : PolMul.Spectral ℂ) (s : Finset I) (S : I → Tensor ℂ E F G) (c : I → ℝ)
    (hc : ∀ i ∈ s, value φ (S i) ≤ c i) (T : Tensor ℂ E F G) :
    value φ T ≤ value φ (T + ∑ i ∈ s, S i) + ∑ i ∈ s, c i := by
  apply NNN7.remove_sum_value
  intro i hi Q
  exact (NNN7.remove_correction_value φ Q (S i) (S i) (NNN7.identity_restriction _)).trans
    (add_le_add_right (hc i hi) _)

theorem telescoped_value {I J K : Type} (φ : PolMul.Spectral ℂ) (T : Tensor ℂ X Y Z)
    (s : Finset I) (t : Finset J) (u : Finset K)
    (P : I → Operator (BondAB A B X Y)) (Q : J → Operator (BondBC B C Y Z))
    (R : K → Operator (BondCA C A Z X)) (a : I → ℝ) (b : J → ℝ) (c : K → ℝ)
    (ha : ∀ i ∈ s, value φ (contract (A := A) (B := B) (C := C) T (P i) (identity _) (identity _)) ≤ a i)
    (hb : ∀ j ∈ t, value φ (contract (A := A) (B := B) (C := C) T (identity _ + ∑ i ∈ s, P i)
      (Q j) (identity _ + ∑ k ∈ u, R k)) ≤ b j)
    (hc : ∀ k ∈ u, value φ (contract (A := A) (B := B) (C := C) T (identity _ + ∑ i ∈ s, P i) (identity _) (R k)) ≤ c k) :
    value φ (contract (A := A) (B := B) (C := C) T (identity _) (identity _) (identity _)) ≤
      value φ (contract (A := A) (B := B) (C := C) T (identity _ + ∑ i ∈ s, P i)
        (identity _ + ∑ j ∈ t, Q j) (identity _ + ∑ k ∈ u, R k)) +
      (∑ i ∈ s, a i) + (∑ j ∈ t, b j) + ∑ k ∈ u, c k := by
  have h1 := remove_sum_bound φ s (fun i => contract (A := A) (B := B) (C := C) T (P i) (identity _) (identity _)) a ha
    (contract (A := A) (B := B) (C := C) T (identity _) (identity _) (identity _))
  have h2 := remove_sum_bound φ u
    (fun k => contract (A := A) (B := B) (C := C) T (identity _ + ∑ i ∈ s, P i) (identity _) (R k)) c hc
    (contract (A := A) (B := B) (C := C) T (identity _) (identity _) (identity _) +
      ∑ i ∈ s, contract (A := A) (B := B) (C := C) T (P i) (identity _) (identity _))
  have h3 := remove_sum_bound φ t
    (fun j => contract (A := A) (B := B) (C := C) T (identity _ + ∑ i ∈ s, P i) (Q j) (identity _ + ∑ k ∈ u, R k)) b hb
    (contract (A := A) (B := B) (C := C) T (identity _) (identity _) (identity _) +
      (∑ i ∈ s, contract (A := A) (B := B) (C := C) T (P i) (identity _) (identity _)) +
      ∑ k ∈ u, contract (A := A) (B := B) (C := C) T (identity _ + ∑ i ∈ s, P i) (identity _) (R k))
  rw [← telescope_sum] at h3
  linarith

/-- The head is priced by its three separate factor dimensions, including zero. -/
theorem head_value {P Q R : Type} [Fintype P] [Fintype Q] [Fintype R]
    (φ : PolMul.Spectral ℂ) (T : Tensor ℂ X Y Z)
    (Uab Vab : P → BondAB A B X Y → ℂ)
    (Ubc Vbc : Q → BondBC B C Y Z → ℂ)
    (Uca Vca : R → BondCA C A Z X → ℂ) :
    value φ (contract (A := A) (B := B) (C := C) T (factor Uab Vab) (factor Ubc Vbc) (factor Uca Vca)) ≤
      (Fintype.card R : ℝ) ^ Foundations.PairUnitExponents.theta φ 1 *
      (Fintype.card P : ℝ) ^ Foundations.PairUnitExponents.theta φ 2 *
      (Fintype.card Q : ℝ) ^ Foundations.PairUnitExponents.theta φ 0 :=
  (value_mono φ (restricts_degenerates _ _
    (compressed_restriction T Uab Vab Ubc Vbc Uca Vca))).trans (NNN10.value_mm_card_le φ)

end OM.NNN11.Network
