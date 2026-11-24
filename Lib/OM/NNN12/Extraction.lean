import Lib.OM.NNN12.Excess
import Lib.OM.NNN12.Layout
import Lib.OM.NNN11.OuterPrices

/-! Applying an all-format bound to the literal extracted residual, at the
same spectral point and in its original physical party order. Complements
are arbitrary operators on the other two bonds. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN12
open CoordinateTensor OM.NNN.Raw NNN11.Network NNN11.SlotExtraction
open NNN11 (card_eq_change_fintypes value_le_change_fintypes outputs_binary_card)
open NNN11.ExtractionAB (X)
open Foundations.PairUnitExponents Codes
set_option maxHeartbeats 1500000

theorem bound_of_card (φ : PolMul.Spectral ℂ) {F : Shape → ℝ}
    (hb : ∀ (x : Shape) (T : DyadicTensor x), value φ T ≤ (2 : ℝ) ^ F x)
    {I J K : Type} [Fintype I] [Fintype J] [Fintype K] (x : Shape)
    (hi : Fintype.card I = 2 ^ x 0) (hj : Fintype.card J = 2 ^ x 1)
    (hk : Fintype.card K = 2 ^ x 2) (T : Tensor ℂ I J K) : value φ T ≤ (2 : ℝ) ^ F x := by
  let ei : X (x 0) ≃ I := Fintype.equivOfCardEq (by simp [X, hi])
  let ej : X (x 1) ≃ J := Fintype.equivOfCardEq (by simp [X, hj])
  let ek : X (x 2) ≃ K := Fintype.equivOfCardEq (by simp [X, hk])
  have hh := hb x (fun a b c => T (ei a) (ej b) (ek c))
  rwa [value_reindex] at hh

lemma edge_price {s w A θ t : ℝ} (E : ℕ) (hθ : θ ≤ t)
    (he : s ≤ w * ((2 : ℝ) ^ E) ^ θ) (hw : w ≤ (2 : ℝ) ^ A) :
    s ≤ (2 : ℝ) ^ (A + t * E) := by
  have hh := NNN11.residual_edge_price (m := 1) (f := A) (g := 0) E hθ he
    (by simpa using! hw)
  simpa using! hh

namespace BondLayout
variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C]
  {q k x y z N : ℕ} [Fact q.Prime]

theorem full_AB_of_bound (L : BondLayout q k A B x y N) (c : Word q N)
    (φ : PolMul.Spectral ℂ) {F : Shape → ℝ}
    (hb : ∀ (v : Shape) (U : DyadicTensor v), value φ U ≤ (2 : ℝ) ^ F v)
    (t : ℝ) (ht : theta φ 2 ≤ t) (T : Tensor ℂ (X x) (X y) (X z))
    (Q : Operator (BondBC B C (X y) (X z))) (R : Operator (BondCA C A (X z) (X x))) :
    let p := Fintype.card A + Fintype.card B + Fintype.card C
    value φ (contract T (L.kernel c) Q R) ≤
      (2 : ℝ) ^ (F ![p * x - k * weight c, p * y - k * weight c, p * z] + t * (k * weight c)) := by
  dsimp only
  let σ := Cyclic.permutation L.coordinates c
  let active := Cyclic.active L.coordinates c
  let W := NNN11.ExtractionAB.residual σ active T (NNN11.ExtractionAB.productComplement active Q R)
  have heq : Fintype.card (EqualSlots σ active) = k * weight c := L.crossings c
  have hw := bound_of_card φ hb
    ![(Fintype.card A + Fintype.card B + Fintype.card C) * x - k * weight c,
      (Fintype.card A + Fintype.card B + Fintype.card C) * y - k * weight c,
      (Fintype.card A + Fintype.card B + Fintype.card C) * z]
    (by
      have hd := NNN11.ExtractionAB.residualX_card (C := C) σ active
      rw [heq] at hd
      exact card_eq_change_fintypes hd)
    (by
      have hd := NNN11.ExtractionAB.residualY_card (C := C) σ active
      rw [heq] at hd
      exact card_eq_change_fintypes hd)
    (outputs_binary_card z) W
  have he := NNN11.ExtractionAB.permutation_network_edge_value σ active
    (Cyclic.stable L.coordinates c) (Cyclic.fixed L.coordinates c) φ T Q R
  simp only [Fintype.card_fun, ZMod.card, heq, Nat.cast_pow, Nat.cast_ofNat] at he
  have hh := edge_price (k * weight c) ht he (value_le_change_fintypes φ _ hw)
  simpa only [Nat.cast_mul] using! value_le_change_fintypes φ _ hh

theorem full_BC_of_bound (L : BondLayout q k B C y z N) (c : Word q N)
    (φ : PolMul.Spectral ℂ) {F : Shape → ℝ}
    (hb : ∀ (v : Shape) (U : DyadicTensor v), value φ U ≤ (2 : ℝ) ^ F v)
    (t : ℝ) (ht : theta φ 0 ≤ t) (T : Tensor ℂ (X x) (X y) (X z))
    (P : Operator (BondAB A B (X x) (X y))) (R : Operator (BondCA C A (X z) (X x))) :
    let p := Fintype.card A + Fintype.card B + Fintype.card C
    value φ (contract T P (L.kernel c) R) ≤
      (2 : ℝ) ^ (F ![p * x, p * y - k * weight c, p * z - k * weight c] + t * (k * weight c)) := by
  dsimp only
  let σ := Cyclic.permutation L.coordinates c
  let active := Cyclic.active L.coordinates c
  let W := NNN11.ExtractionBC.residual σ active T (NNN11.ExtractionBC.productComplement active P R)
  have heq : Fintype.card (EqualSlots σ active) = k * weight c := L.crossings c
  have hw := bound_of_card φ hb
    ![(Fintype.card A + Fintype.card B + Fintype.card C) * x,
      (Fintype.card A + Fintype.card B + Fintype.card C) * y - k * weight c,
      (Fintype.card A + Fintype.card B + Fintype.card C) * z - k * weight c]
    (outputs_binary_card x)
    (by
      have hd := NNN11.ExtractionBC.residualY_card (A := A) σ active
      rw [heq] at hd
      exact card_eq_change_fintypes hd)
    (by
      have hd := NNN11.ExtractionBC.residualZ_card (A := A) σ active
      rw [heq] at hd
      exact card_eq_change_fintypes hd) W
  have he := NNN11.ExtractionBC.permutation_network_edge_value σ active
    (Cyclic.stable L.coordinates c) (Cyclic.fixed L.coordinates c) φ T P R
  simp only [Fintype.card_fun, ZMod.card, heq, Nat.cast_pow, Nat.cast_ofNat] at he
  have hh := edge_price (k * weight c) ht he (value_le_change_fintypes φ _ hw)
  simpa only [Nat.cast_mul] using! value_le_change_fintypes φ _ hh

theorem full_CA_of_bound (L : BondLayout q k C A z x N) (c : Word q N)
    (φ : PolMul.Spectral ℂ) {F : Shape → ℝ}
    (hb : ∀ (v : Shape) (U : DyadicTensor v), value φ U ≤ (2 : ℝ) ^ F v)
    (t : ℝ) (ht : theta φ 1 ≤ t) (T : Tensor ℂ (X x) (X y) (X z))
    (P : Operator (BondAB A B (X x) (X y))) (Q : Operator (BondBC B C (X y) (X z))) :
    let p := Fintype.card A + Fintype.card B + Fintype.card C
    value φ (contract T P Q (L.kernel c)) ≤
      (2 : ℝ) ^ (F ![p * x - k * weight c, p * y, p * z - k * weight c] + t * (k * weight c)) := by
  dsimp only
  let σ := Cyclic.permutation L.coordinates c
  let active := Cyclic.active L.coordinates c
  let W := NNN11.ExtractionCA.residual σ active T (NNN11.ExtractionCA.productComplement active P Q)
  have heq : Fintype.card (EqualSlots σ active) = k * weight c := L.crossings c
  have hw := bound_of_card φ hb
    ![(Fintype.card A + Fintype.card B + Fintype.card C) * x - k * weight c,
      (Fintype.card A + Fintype.card B + Fintype.card C) * y,
      (Fintype.card A + Fintype.card B + Fintype.card C) * z - k * weight c]
    (by
      have hd := NNN11.ExtractionCA.residualX_card (B := B) σ active
      rw [heq] at hd
      exact card_eq_change_fintypes hd)
    (outputs_binary_card y)
    (by
      have hd := NNN11.ExtractionCA.residualZ_card (B := B) σ active
      rw [heq] at hd
      exact card_eq_change_fintypes hd) W
  have he := NNN11.ExtractionCA.permutation_network_edge_value σ active
    (Cyclic.stable L.coordinates c) (Cyclic.fixed L.coordinates c) φ T P Q
  simp only [Fintype.card_fun, ZMod.card, heq, Nat.cast_pow, Nat.cast_ofNat] at he
  have hh := edge_price (k * weight c) ht he (value_le_change_fintypes φ _ hw)
  simpa only [Nat.cast_mul] using! value_le_change_fintypes φ _ hh

end BondLayout
end OM.NNN12
