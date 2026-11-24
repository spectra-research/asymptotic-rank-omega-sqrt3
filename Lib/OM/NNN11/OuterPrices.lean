import Lib.OM.NNN11.InnerSpectral
import Lib.OM.NNN11.Interpolation

/-! Actual residual tensors in the outer shape cone and interpolated prices. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN11
open CoordinateTensor OM.NNN.Raw OM.NNN2 Network SlotExtraction
open ExtractionAB (X)
open Foundations.PairUnitExponents
set_option maxHeartbeats 500000

lemma card_eq_change_fintypes {E : Type} {i j : Fintype E} {n : ℕ}
    (h : @Fintype.card E i = n) : @Fintype.card E j = n := by
  cases Subsingleton.elim i j
  exact h

lemma outputs_binary_card {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] (l : ℕ) :
    Fintype.card (Outputs A B C (X l)) = 2 ^ ((Fintype.card A + Fintype.card B + Fintype.card C) * l) := by
  simp only [Outputs, X, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    ZMod.card, ← pow_mul, ← pow_add]
  congr 1
  ring

lemma residual_edge_price {s w m f g θ t : ℝ} (H : ℕ) (hθ : θ ≤ t)
    (he : s ≤ w * ((2 : ℝ) ^ H) ^ θ)
    (hw : w ≤ (2 : ℝ) ^ (m * f - H * g)) :
    s ≤ (2 : ℝ) ^ (m * f + (t - g) * H) := by
  have hedge : ((2 : ℝ) ^ H) ^ θ ≤ (2 : ℝ) ^ ((H : ℝ) * t) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    exact mul_le_mul_of_nonneg_left hθ (Nat.cast_nonneg _)
  apply (he.trans (mul_le_mul hw hedge (by positivity) (by positivity))).trans_eq
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

namespace BondLayout
variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] {l N : ℕ}

theorem recursive_BC (L : BondLayout B C l l N) (hN : N ≤ 7 * l)
    (hp : Fintype.card A + Fintype.card B + Fintype.card C = 70) (c : Word N)
    (φ : PolMul.Spectral ℂ) (t : Fin 3 → ℝ) (ht : ∀ i, t i ∈ Set.Icc (1 / 4 : ℝ) 1)
    (hθ : ∀ i, theta φ i ≤ t i) (hs : t 0 + t 1 + t 2 = (9 : ℝ) / 4)
    (T : Tensor ℂ (X l) (X l) (X l))
    (P : Operator (BondAB A B (X l) (X l))) (R : Operator (BondCA C A (X l) (X l))) :
    value φ (contract T P (L.kernel c) R) ≤
      (2 : ℝ) ^ ((70 * l : ℕ) * innerF (t 0) + (t 0 - innerG (t 0)) * (2 * weight c)) := by
  let σ := MixedCrossings.permutation L.coordinates c
  let active := MixedCrossings.active L.coordinates c
  let W := ExtractionBC.residual σ active T (ExtractionBC.productComplement active P R)
  have heq : Fintype.card (EqualSlots σ active) = 2 * weight c := L.crossings c
  have hc : 5 * (2 * weight c) ≤ 70 * l := by have hw := weight_le c; omega
  have hw : value φ W ≤ (2 : ℝ) ^ ((70 * l : ℕ) * innerF (t 0) - (2 * weight c : ℕ) * innerG (t 0)) := by
    apply rect_spectral_A (70 * l) (2 * weight c) hc _ _ _ φ t ht hθ hs W
    · rw [outputs_binary_card, hp]
    · have hd := ExtractionBC.residualY_card (A := A) σ active
      rw [hp, heq] at hd
      exact card_eq_change_fintypes hd
    · have hd := ExtractionBC.residualZ_card (A := A) σ active
      rw [hp, heq] at hd
      exact card_eq_change_fintypes hd
  have he := ExtractionBC.permutation_network_edge_value σ active
    (MixedCrossings.stable L.coordinates c) (MixedCrossings.fixed L.coordinates c) φ T P R
  simp only [Fintype.card_fun, ZMod.card, heq, Nat.cast_pow, Nat.cast_ofNat] at he
  have hb := residual_edge_price (2 * weight c) (hθ 0) he
    (value_le_change_fintypes φ _ hw)
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using! value_le_change_fintypes φ _ hb

theorem recursive_CA (L : BondLayout C A l l N) (hN : N ≤ 7 * l)
    (hp : Fintype.card A + Fintype.card B + Fintype.card C = 70) (c : Word N)
    (φ : PolMul.Spectral ℂ) (t : Fin 3 → ℝ) (ht : ∀ i, t i ∈ Set.Icc (1 / 4 : ℝ) 1)
    (hθ : ∀ i, theta φ i ≤ t i) (hs : t 0 + t 1 + t 2 = (9 : ℝ) / 4)
    (T : Tensor ℂ (X l) (X l) (X l))
    (P : Operator (BondAB A B (X l) (X l))) (Q : Operator (BondBC B C (X l) (X l))) :
    value φ (contract T P Q (L.kernel c)) ≤
      (2 : ℝ) ^ ((70 * l : ℕ) * innerF (t 1) + (t 1 - innerG (t 1)) * (2 * weight c)) := by
  let σ := MixedCrossings.permutation L.coordinates c
  let active := MixedCrossings.active L.coordinates c
  let W := ExtractionCA.residual σ active T (ExtractionCA.productComplement active P Q)
  have heq : Fintype.card (EqualSlots σ active) = 2 * weight c := L.crossings c
  have hc : 5 * (2 * weight c) ≤ 70 * l := by have hw := weight_le c; omega
  have hw : value φ W ≤ (2 : ℝ) ^ ((70 * l : ℕ) * innerF (t 1) - (2 * weight c : ℕ) * innerG (t 1)) := by
    apply rect_spectral_B (70 * l) (2 * weight c) hc _ _ _ φ t ht hθ hs W
    · have hd := ExtractionCA.residualX_card (B := B) σ active
      rw [hp, heq] at hd
      exact card_eq_change_fintypes hd
    · rw [outputs_binary_card, hp]
    · have hd := ExtractionCA.residualZ_card (B := B) σ active
      rw [hp, heq] at hd
      exact card_eq_change_fintypes hd
  have he := ExtractionCA.permutation_network_edge_value σ active
    (MixedCrossings.stable L.coordinates c) (MixedCrossings.fixed L.coordinates c) φ T P Q
  simp only [Fintype.card_fun, ZMod.card, heq, Nat.cast_pow, Nat.cast_ofNat] at he
  have hb := residual_edge_price (2 * weight c) (hθ 1) he
    (value_le_change_fintypes φ _ hw)
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using! value_le_change_fintypes φ _ hb

theorem outer_BC (L : BondLayout B C l l N) (hN : N ≤ 7 * l)
    (hp : Fintype.card A + Fintype.card B + Fintype.card C = 70) (c : Word N)
    (φ : PolMul.Spectral ℂ) (t : Fin 3 → ℝ) (ht : ∀ i, t i ∈ Set.Icc (1 / 4 : ℝ) 1)
    (hθ : ∀ i, theta φ i ≤ t i) (hs : t 0 + t 1 + t 2 = (9 : ℝ) / 4)
    (T : Tensor ℂ (X l) (X l) (X l))
    (P : Operator (BondAB A B (X l) (X l))) (R : Operator (BondCA C A (X l) (X l))) :
    value φ (contract T P (L.kernel c) R) ≤
      (2 : ℝ) ^ (70 * l * outerA (t 0) + 2 * outerD (t 0) * weight c) := by
  have hraw := L.full_BC c φ t hθ hs T P R
  rw [hp] at hraw
  have hsrc : t 2 * l + t 1 * l = (9 / 4 - t 0) * l := by nlinarith only [congrArg (fun s : ℝ => s * l) hs]
  rw [hsrc] at hraw
  have hrect := L.recursive_BC hN hp c φ t ht hθ hs T P R
  have hstar : value φ (contract T P (L.kernel c) R) ≤
      (2 : ℝ) ^ ((70 * l : ℕ) * (9 / 4 - t 0) + (2 * t 0 - 9 / 4) * (2 * weight c)) := by
    apply hraw.trans_eq
    dsimp [wordPrice]
    push_cast
    congr 1
    ring
  apply (outer_interpolation hstar hrect).trans_eq
  push_cast
  congr 1
  ring

theorem outer_CA (L : BondLayout C A l l N) (hN : N ≤ 7 * l)
    (hp : Fintype.card A + Fintype.card B + Fintype.card C = 70) (c : Word N)
    (φ : PolMul.Spectral ℂ) (t : Fin 3 → ℝ) (ht : ∀ i, t i ∈ Set.Icc (1 / 4 : ℝ) 1)
    (hθ : ∀ i, theta φ i ≤ t i) (hs : t 0 + t 1 + t 2 = (9 : ℝ) / 4)
    (T : Tensor ℂ (X l) (X l) (X l))
    (P : Operator (BondAB A B (X l) (X l))) (Q : Operator (BondBC B C (X l) (X l))) :
    value φ (contract T P Q (L.kernel c)) ≤
      (2 : ℝ) ^ (70 * l * outerA (t 1) + 2 * outerD (t 1) * weight c) := by
  have hraw := L.full_CA c φ t hθ hs T P Q
  rw [hp] at hraw
  have hsrc : t 2 * l + t 0 * l = (9 / 4 - t 1) * l := by nlinarith only [congrArg (fun s : ℝ => s * l) hs]
  rw [hsrc] at hraw
  have hrect := L.recursive_CA hN hp c φ t ht hθ hs T P Q
  have hstar : value φ (contract T P Q (L.kernel c)) ≤
      (2 : ℝ) ^ ((70 * l : ℕ) * (9 / 4 - t 1) + (2 * t 1 - 9 / 4) * (2 * weight c)) := by
    apply hraw.trans_eq
    dsimp [wordPrice]
    push_cast
    congr 1
    ring
  apply (outer_interpolation hstar hrect).trans_eq
  push_cast
  congr 1
  ring

end BondLayout
end OM.NNN11
