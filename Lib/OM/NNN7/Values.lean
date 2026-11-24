import Lib.OM.NNN7.Restriction

/-! Pay each grouped correction at the same spectral point, using its literal
negative local map. No subtraction in the restriction preorder is assumed. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN7
open CoordinateTensor OM.NNN.Raw OM.NNN2 OM.NNN3 Foundations.PairUnitExponents
set_option maxHeartbeats 1000000

variable {I J K A B C : Type} [Fintype I] [Fintype J] [Fintype K]
  [Fintype A] [Fintype B] [Fintype C]

lemma identity_restriction (P : Tensor ℂ A B C) : Restricts P P := by
  refine ⟨identityRows A, identityRows B, identityRows C, ?_⟩
  funext a b c
  simp [mapTensor, identityRows, ite_mul, mul_ite, Finset.sum_ite_irrel]

theorem remove_correction_value (φ : PolMul.Spectral ℂ)
    (P Q : Tensor ℂ A B C) (S : Tensor ℂ I J K) (hQ : Restricts S Q) :
    value φ P ≤ value φ (P + Q) + value φ S := by
  have h := restricts_add (identity_restriction (P + Q)) (restricts_neg hQ)
  simp only [add_neg_cancel_right] at h
  have hv := value_mono φ (restricts_degenerates _ _ h)
  rwa [value_add] at hv

omit [Fintype I] [Fintype J] [Fintype K] in
lemma remove_sum_value {D : Type} (φ : PolMul.Spectral ℂ) (s : Finset D)
    (R : D → Tensor ℂ A B C) (c : D → ℝ)
    (h : ∀ h ∈ s, ∀ P : Tensor ℂ A B C, value φ P ≤ value φ (P + R h) + c h)
    (P : Tensor ℂ A B C) :
    value φ P ≤ value φ (P + ∑ h ∈ s, R h) + ∑ h ∈ s, c h := by
  induction s using Finset.induction_on generalizing P with
  | empty => simp
  | @insert a s ha ih =>
    have h1 := h a (Finset.mem_insert_self _ _) P
    have h2 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi)) (P + R a)
    have he : (P + R a) + ∑ i ∈ s, R i = P + ∑ i ∈ insert a s, R i := by
      rw [Finset.sum_insert ha]
      abel
    rw [he] at h2
    simp only [Finset.sum_insert ha] at h2 ⊢
    linarith only [h1, h2]

variable {D : Type} [Fintype D] [LinearOrder D] {X : D → Type}
  [∀ h, Fintype (X h)] [∀ h, Nonempty (X h)]

/-- The ordinary digitwise inequality (23), before rewriting cardinalities. -/
theorem digitwise_value (φ : PolMul.Spectral ℂ) (T : Cube ℂ (∀ h, X h)) :
    value φ (tensorProduct T T) ≤
      value φ (squareSource (∀ h, X h) (∀ h, Sym2 (X h))) +
        ∑ h, value φ (squareSource ((∀ g, X g) × Rest X h) (X h)) := by
  have h := remove_sum_value φ Finset.univ (correction T)
    (fun h => value φ (squareSource ((∀ g, X g) × Rest X h) (X h)))
    (fun h _ P => remove_correction_value φ P (correction T h) _
      (correction_restriction T h (Classical.choice (inferInstance : Nonempty (X h)))))
    (tensorProduct T T)
  rw [← compressed_payload T] at h
  have hm := value_map_le φ (squareSource (∀ h, X h) (∀ h, Sym2 (X h)))
    (compressedLeft T) (compressedRight T) (identityRows ((∀ h, X h) × (∀ h, X h)))
  linarith only [h, hm]

lemma value_squareSource_card {Y R : Type} [Fintype Y] [Fintype R] [Nonempty Y] [Nonempty R]
    (φ : PolMul.Spectral ℂ) :
    value φ (squareSource Y R) =
      (Fintype.card Y : ℝ) ^ theta φ 1 * (Fintype.card R : ℝ) ^ theta φ 2 *
        (Fintype.card Y : ℝ) ^ theta φ 0 := by
  let n : ℕ+ := ⟨Fintype.card Y, Fintype.card_pos⟩
  let r : ℕ+ := ⟨Fintype.card R, Fintype.card_pos⟩
  rw [value_squareSource φ (n := n) (m := r) (Fintype.equivFin Y).symm
    (Fintype.equivFin R).symm, OM.Omega.eval_matMul]
  rfl

/-- Exact rectangular prices (25); each orientation exponent belongs to the same φ. -/
theorem digitwise_price (φ : PolMul.Spectral ℂ) (T : Cube ℂ (∀ h, X h)) :
    value φ T ^ 2 ≤
      (Fintype.card (∀ h, X h) : ℝ) ^ theta φ 1 *
        (Fintype.card (∀ h, Sym2 (X h)) : ℝ) ^ theta φ 2 *
          (Fintype.card (∀ h, X h) : ℝ) ^ theta φ 0 +
      ∑ h, (Fintype.card ((∀ g, X g) × Rest X h) : ℝ) ^ theta φ 1 *
        (Fintype.card (X h) : ℝ) ^ theta φ 2 *
          (Fintype.card ((∀ g, X g) × Rest X h) : ℝ) ^ theta φ 0 := by
  letI (h : D) : Nonempty (Sym2 (X h)) :=
    ⟨s(Classical.choice (inferInstance : Nonempty (X h)), Classical.choice (inferInstance : Nonempty (X h)))⟩
  let n : ℕ+ := ⟨Fintype.card (∀ h, X h), Fintype.card_pos⟩
  have h := digitwise_value φ T
  rw [value_cubeSquare φ (n := n) (Fintype.equivFin (∀ h, X h)).symm] at h
  simpa only [value_squareSource_card] using! h

end OM.NNN7
