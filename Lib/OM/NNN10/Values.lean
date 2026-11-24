import Lib.OM.NNN10.Extraction
import Lib.OM.NNN8.Values

/-! All charges use a single spectral point, including the retained copy. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN10
open CoordinateTensor OM.NNN.Raw OM.NNN2 OM.NNN3 Foundations.PairUnitExponents
open NNN8 (maskKernel Selected Remaining fill BinaryWord binary_word_card remaining_card selected_card correction_price)
set_option maxHeartbeats 1000000

lemma value_mm_card_le {R Q P : Type} [Fintype R] [Fintype Q] [Fintype P]
    (φ : PolMul.Spectral ℂ) : value φ (mm R Q P) ≤
      (Fintype.card R : ℝ) ^ theta φ 1 * (Fintype.card P : ℝ) ^ theta φ 2 *
        (Fintype.card Q : ℝ) ^ theta φ 0 := by
  rcases isEmpty_or_nonempty R with hR | hR
  · letI := hR
    have hz : mm R Q P = 0 := by funext a b c; exact isEmptyElim a.1
    rw [hz, value_zero]
    positivity
  rcases isEmpty_or_nonempty Q with hQ | hQ
  · letI := hQ
    have hz : mm R Q P = 0 := by funext a b c; exact isEmptyElim b.1
    rw [hz, value_zero]
    positivity
  rcases isEmpty_or_nonempty P with hP | hP
  · letI := hP
    have hz : mm R Q P = 0 := by funext a b c; exact isEmptyElim a.2
    rw [hz, value_zero]
    positivity
  letI := hR
  letI := hQ
  letI := hP
  let r : ℕ+ := ⟨Fintype.card R, Fintype.card_pos⟩
  let q : ℕ+ := ⟨Fintype.card Q, Fintype.card_pos⟩
  let p : ℕ+ := ⟨Fintype.card P, Fintype.card_pos⟩
  exact (value_mm φ (n := r) (p := q) (m := p) (Fintype.equivFin R).symm
    (Fintype.equivFin Q).symm (Fintype.equivFin P).symm).le

lemma value_smul_le {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    (φ : PolMul.Spectral ℂ) (T : Tensor ℂ A B C) (z : ℂ) : value φ (z • T) ≤ value φ T :=
  value_mono φ (restricts_degenerates _ _
    (NNN8.restricts_smul (NNN7.identity_restriction T) z))

lemma remove_sum_bound {I X : Type} [Fintype X] (φ : PolMul.Spectral ℂ)
    (s : Finset I) (F : I → Cube ℂ X) (c : I → ℝ)
    (hc : ∀ i ∈ s, value φ (F i) ≤ c i) (P : Cube ℂ X) :
    value φ P ≤ value φ (P + ∑ i ∈ s, F i) + ∑ i ∈ s, c i := by
  apply NNN7.remove_sum_value
  intro i hi Q
  exact (NNN7.remove_correction_value φ Q (F i) (F i) (NNN7.identity_restriction _)).trans
    (add_le_add_right (hc i hi) _)

theorem telescoped_value {I J K X : Type} [Fintype X]
    (φ : PolMul.Spectral ℂ) (T : Cube ℂ X)
    (s : Finset I) (t : Finset J) (u : Finset K)
    (A : I → Kernel X) (B : J → Kernel X) (C : K → Kernel X)
    (a : I → ℝ) (b : J → ℝ) (c : K → ℝ)
    (ha : ∀ i ∈ s, value φ (contract T (A i) straight straight) ≤ a i)
    (hb : ∀ j ∈ t, value φ (contract T (straight + ∑ i ∈ s, A i)
      (B j) (straight + ∑ k ∈ u, C k)) ≤ b j)
    (hc : ∀ k ∈ u, value φ (contract T (straight + ∑ i ∈ s, A i) straight (C k)) ≤ c k) :
    value φ (cube T) ≤
      value φ (contract T (straight + ∑ i ∈ s, A i)
        (straight + ∑ j ∈ t, B j) (straight + ∑ k ∈ u, C k)) +
      (∑ i ∈ s, a i) + (∑ j ∈ t, b j) + ∑ k ∈ u, c k := by
  have h1 := remove_sum_bound φ s (fun i => contract T (A i) straight straight) a ha (cube T)
  have h2 := remove_sum_bound φ u
    (fun k => contract T (straight + ∑ i ∈ s, A i) straight (C k)) c hc
    (cube T + ∑ i ∈ s, contract T (A i) straight straight)
  have h3 := remove_sum_bound φ t
    (fun j => contract T (straight + ∑ i ∈ s, A i) (B j) (straight + ∑ k ∈ u, C k)) b hb
    (cube T + (∑ i ∈ s, contract T (A i) straight straight) +
      ∑ k ∈ u, contract T (straight + ∑ i ∈ s, A i) straight (C k))
  rw [← telescope_sum] at h3
  linarith

lemma full_residual_card (l : ℕ) (s : Finset (Fin l)) :
    (Fintype.card (FullResidual (fun _ : Fin l => ZMod 2) s) : ℝ) =
      ((2 : ℝ) ^ l) ^ (3 : ℕ) / (2 : ℝ) ^ s.card := by
  have hs : s.card ≤ l := by simpa using! Finset.card_le_univ s
  simp only [FullResidual, Fintype.card_prod]
  change ((Fintype.card (BinaryWord l) * Fintype.card (BinaryWord l) *
    Fintype.card (Remaining (fun _ : Fin l => ZMod 2) s) : ℕ) : ℝ) = _
  rw [binary_word_card, remaining_card]
  push_cast
  apply (eq_div_iff (by positivity : (2 : ℝ) ^ s.card ≠ 0)).2
  rw [mul_assoc, mul_assoc, ← pow_add, Nat.sub_add_cancel hs]
  ring

def starPrice (l m w : ℕ) (a t : ℝ) : ℝ :=
  (((2 : ℝ) ^ l) ^ m / (2 : ℝ) ^ w) ^ a * ((2 : ℝ) ^ w) ^ t

theorem fullBC_price (φ : PolMul.Spectral ℂ) (l : ℕ) (T : Cube ℂ (BinaryWord l))
    (s : Finset (Fin l)) (A C : Kernel (BinaryWord l)) :
    value φ (contract T A (maskKernel s) C) ≤ starPrice l 3 s.card
      (theta φ 1 + theta φ 2) (theta φ 0) := by
  have h := value_mono φ (restricts_degenerates _ _ (fullBC_restriction T s A C (fun _ => 0)))
  refine (h.trans (value_mm_card_le φ)).trans_eq ?_
  rw [full_residual_card, selected_card]
  push_cast
  rw [← Real.rpow_add (by positivity)]
  rfl

theorem fullCA_price (φ : PolMul.Spectral ℂ) (l : ℕ) (T : Cube ℂ (BinaryWord l))
    (s : Finset (Fin l)) (A B : Kernel (BinaryWord l)) :
    value φ (contract T A B (maskKernel s)) ≤ starPrice l 3 s.card
      (theta φ 0 + theta φ 2) (theta φ 1) := by
  have h := value_mono φ (restricts_degenerates _ _ (fullCA_restriction T s A B (fun _ => 0)))
  refine (h.trans (value_mm_card_le φ)).trans_eq ?_
  rw [full_residual_card, selected_card]
  push_cast
  dsimp [starPrice]
  rw [Real.rpow_add (by positivity)]
  ring

theorem retainedAB_price (φ : PolMul.Spectral ℂ) (l : ℕ) (T : Cube ℂ (BinaryWord l))
    (s : Finset (Fin l)) :
    value φ (contract T (maskKernel s) straight straight) ≤
      starPrice l 2 s.card (theta φ 0 + theta φ 1) (theta φ 2) * value φ T := by
  rw [value_retainedAB]
  have h := value_mono φ (restricts_degenerates _ _ (NNN8.correction_restriction T s (fun _ => 0)))
  rw [correction_price] at h
  exact mul_le_mul_of_nonneg_right h (φ.nonneg _)

end OM.NNN10
