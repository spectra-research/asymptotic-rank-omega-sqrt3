import Lib.OM.NNN13.Layout
import Lib.OM.NNN12.Extraction

/-! Recursive pricing of the last group's residual at the original spectral
point. The copies opposite the last physical bond remain actual factors.
The full-group versions are reused directly from NNN12.BondLayout. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN13
open CoordinateTensor OM.NNN.Raw OM.NNN2 NNN11.Network
open NNN11 (value_le_change_fintypes restricts_by_coordinates)
open NNN11.ExtractionAB (X)
open Foundations.PairUnitExponents NNN12 NNN12.Codes
set_option maxHeartbeats 1500000

variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C]
  {q d x y z N : ℕ} [Fact q.Prime]

theorem retained_AB_of_bound (L : NNN12.BondLayout q d A B x y N) (c : Word q N)
    (φ : PolMul.Spectral ℂ) {F : Shape → ℝ}
    (hb : ∀ (v : Shape) (U : DyadicTensor v), value φ U ≤ (2 : ℝ) ^ F v)
    (t : ℝ) (ht : theta φ 2 ≤ t) (T : Tensor ℂ (X x) (X y) (X z)) :
    let m := Fintype.card A + Fintype.card B
    value φ (contract (C := C) T (L.kernel c) (identity _) (identity _)) ≤
      (2 : ℝ) ^ (F ![m * x - d * weight c, m * y - d * weight c, m * z] +
        t * (d * weight c)) * value φ T ^ Fintype.card C := by
  dsimp only
  have hr := restricts_by_coordinates
    (contract (C := Empty) T (L.kernel c) (identity _) (identity _))
    (NNN11.ExtractionAB.addEmpty (A := A) (B := B) _)
    (NNN11.ExtractionAB.addEmpty _) (NNN11.ExtractionAB.addEmpty _)
  rw [NNN11.ExtractionAB.pairAB_as_empty_network] at hr
  have hp := L.full_AB_of_bound (C := Empty) c φ hb t ht T (identity _) (identity _)
  simp only [Fintype.card_eq_zero, add_zero] at hp
  have hh := (value_mono φ (restricts_degenerates _ _ hr)).trans hp
  rw [value_retainedAB]
  exact mul_le_mul_of_nonneg_right (value_le_change_fintypes φ _ hh)
    (pow_nonneg (φ.nonneg _) _)

theorem retained_BC_of_bound (L : NNN12.BondLayout q d B C y z N) (c : Word q N)
    (φ : PolMul.Spectral ℂ) {F : Shape → ℝ}
    (hb : ∀ (v : Shape) (U : DyadicTensor v), value φ U ≤ (2 : ℝ) ^ F v)
    (t : ℝ) (ht : theta φ 0 ≤ t) (T : Tensor ℂ (X x) (X y) (X z)) :
    let m := Fintype.card B + Fintype.card C
    value φ (contract (A := A) T (identity _) (L.kernel c) (identity _)) ≤
      (2 : ℝ) ^ (F ![m * x, m * y - d * weight c, m * z - d * weight c] +
        t * (d * weight c)) * value φ T ^ Fintype.card A := by
  dsimp only
  have hr := restricts_by_coordinates
    (contract (A := Empty) T (identity _) (L.kernel c) (identity _))
    (NNN11.ExtractionBC.addEmpty (B := B) (C := C) _)
    (NNN11.ExtractionBC.addEmpty _) (NNN11.ExtractionBC.addEmpty _)
  rw [NNN11.ExtractionBC.pair_as_empty_network] at hr
  have hp := L.full_BC_of_bound (A := Empty) c φ hb t ht T (identity _) (identity _)
  simp only [Fintype.card_eq_zero, zero_add] at hp
  have hh := (value_mono φ (restricts_degenerates _ _ hr)).trans hp
  rw [value_retainedBC]
  exact mul_le_mul_of_nonneg_right (value_le_change_fintypes φ _ hh)
    (pow_nonneg (φ.nonneg _) _)

theorem retained_CA_of_bound (L : NNN12.BondLayout q d C A z x N) (c : Word q N)
    (φ : PolMul.Spectral ℂ) {F : Shape → ℝ}
    (hb : ∀ (v : Shape) (U : DyadicTensor v), value φ U ≤ (2 : ℝ) ^ F v)
    (t : ℝ) (ht : theta φ 1 ≤ t) (T : Tensor ℂ (X x) (X y) (X z)) :
    let m := Fintype.card A + Fintype.card C
    value φ (contract (B := B) T (identity _) (identity _) (L.kernel c)) ≤
      (2 : ℝ) ^ (F ![m * x - d * weight c, m * y, m * z - d * weight c] +
        t * (d * weight c)) * value φ T ^ Fintype.card B := by
  dsimp only
  have hr := restricts_by_coordinates
    (contract (B := Empty) T (identity _) (identity _) (L.kernel c))
    (NNN11.ExtractionCA.addEmpty (A := A) (C := C) _)
    (NNN11.ExtractionCA.addEmpty _) (NNN11.ExtractionCA.addEmpty _)
  rw [NNN11.ExtractionCA.pair_as_empty_network] at hr
  have hp := L.full_CA_of_bound (B := Empty) c φ hb t ht T (identity _) (identity _)
  simp only [Fintype.card_eq_zero, add_zero] at hp
  have hh := (value_mono φ (restricts_degenerates _ _ hr)).trans hp
  rw [value_retainedCA]
  exact mul_le_mul_of_nonneg_right (value_le_change_fintypes φ _ hh)
    (pow_nonneg (φ.nonneg _) _)

end OM.NNN13
