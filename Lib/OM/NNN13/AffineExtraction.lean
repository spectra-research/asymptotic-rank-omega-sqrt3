import Lib.OM.NNN13.Extraction
import Lib.OM.NNN13.Potential

/-! Affine prices for the actual extracted rectangular tensors. The bounds
are at one fixed spectral point and uniform in the coefficients and in all
complementary bond operators. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN13
open CoordinateTensor OM.NNN.Raw NNN11.Network
open NNN11.ExtractionAB (X)
open Foundations.PairUnitExponents NNN12.Codes
open NNN12 (Shape DyadicTensor)
set_option maxHeartbeats 1500000

def AffineBound (φ : PolMul.Spectral ℂ) (c : Fin 3 → ℝ) : Prop :=
  ∀ (v : Shape) (U : DyadicTensor v), value φ U ≤ (2 : ℝ) ^ plane c (fun i => (v i : ℝ))

theorem affineBound_of_majorant (φ : PolMul.Spectral ℂ) {F : Shape → ℝ} {c : Fin 3 → ℝ}
    (hb : ∀ (v : Shape) (U : DyadicTensor v), value φ U ≤ (2 : ℝ) ^ F v)
    (hc : ∀ v, F v ≤ plane c (fun i => (v i : ℝ))) : AffineBound φ c := by
  intro v U
  exact (hb v U).trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (hc v))

lemma affine_residual_AB (c : Fin 3 → ℝ) (t : ℝ) {m x y z E : ℕ}
    (hEx : E ≤ m * x) (hEy : E ≤ m * y) :
    plane c (fun i => ((![m * x - E, m * y - E, m * z] : Shape) i : ℝ)) + t * E =
      m * plane c ![(x : ℝ), y, z] + (t - c 0 - c 1) * E := by
  dsimp [plane]
  rw [Nat.cast_sub hEx, Nat.cast_sub hEy]
  push_cast
  ring

lemma affine_residual_BC (c : Fin 3 → ℝ) (t : ℝ) {m x y z E : ℕ}
    (hEy : E ≤ m * y) (hEz : E ≤ m * z) :
    plane c (fun i => ((![m * x, m * y - E, m * z - E] : Shape) i : ℝ)) + t * E =
      m * plane c ![(x : ℝ), y, z] + (t - c 1 - c 2) * E := by
  dsimp [plane]
  rw [Nat.cast_sub hEy, Nat.cast_sub hEz]
  push_cast
  ring

lemma affine_residual_CA (c : Fin 3 → ℝ) (t : ℝ) {m x y z E : ℕ}
    (hEx : E ≤ m * x) (hEz : E ≤ m * z) :
    plane c (fun i => ((![m * x - E, m * y, m * z - E] : Shape) i : ℝ)) + t * E =
      m * plane c ![(x : ℝ), y, z] + (t - c 0 - c 2) * E := by
  dsimp [plane]
  rw [Nat.cast_sub hEx, Nat.cast_sub hEz]
  push_cast
  ring

variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C]
  {q d x y z N : ℕ} [Fact q.Prime]

lemma extracted_le (L : NNN12.BondLayout q d A B x y N) (w : Word q N) :
    d * weight w ≤ Fintype.card B * x ∧ d * weight w ≤ Fintype.card A * y := by
  have h₁ := NNN11.SlotExtraction.equalSlots_le_row
    (NNN12.Cyclic.permutation L.coordinates w) (NNN12.Cyclic.active L.coordinates w)
  have h₂ := NNN11.SlotExtraction.equalSlots_le_col
    (NNN12.Cyclic.permutation L.coordinates w) (NNN12.Cyclic.active L.coordinates w)
  rw [L.crossings w] at h₁ h₂
  simpa only [Fintype.card_prod, Fintype.card_fin] using! And.intro h₁ h₂

theorem full_AB_affine (L : NNN12.BondLayout q d A B x y N) (w : Word q N)
    (φ : PolMul.Spectral ℂ) {c : Fin 3 → ℝ} (hb : AffineBound φ c)
    (t : ℝ) (ht : theta φ 2 ≤ t) (T : Tensor ℂ (X x) (X y) (X z))
    (Q : Operator (BondBC B C (X y) (X z))) (R : Operator (BondCA C A (X z) (X x))) :
    value φ (contract T (L.kernel w) Q R) ≤ (2 : ℝ) ^
      ((Fintype.card A + Fintype.card B + Fintype.card C : ℕ) * plane c ![(x : ℝ), y, z] +
        (d * (t - c 0 - c 1)) * weight w) := by
  have hh := L.full_AB_of_bound w φ hb t ht T Q R
  obtain ⟨hEx, hEy⟩ := extracted_le L w
  have hx := hEx.trans (Nat.mul_le_mul_right x (show Fintype.card B ≤
    Fintype.card A + Fintype.card B + Fintype.card C by omega))
  have hy := hEy.trans (Nat.mul_le_mul_right y (show Fintype.card A ≤
    Fintype.card A + Fintype.card B + Fintype.card C by omega))
  dsimp only at hh
  rw [← Nat.cast_mul, affine_residual_AB c t hx hy, Nat.cast_mul] at hh
  convert! hh using 1 <;> congr 1 <;> ring

theorem full_BC_affine (L : NNN12.BondLayout q d B C y z N) (w : Word q N)
    (φ : PolMul.Spectral ℂ) {c : Fin 3 → ℝ} (hb : AffineBound φ c)
    (t : ℝ) (ht : theta φ 0 ≤ t) (T : Tensor ℂ (X x) (X y) (X z))
    (P : Operator (BondAB A B (X x) (X y))) (R : Operator (BondCA C A (X z) (X x))) :
    value φ (contract T P (L.kernel w) R) ≤ (2 : ℝ) ^
      ((Fintype.card A + Fintype.card B + Fintype.card C : ℕ) * plane c ![(x : ℝ), y, z] +
        (d * (t - c 1 - c 2)) * weight w) := by
  have hh := L.full_BC_of_bound w φ hb t ht T P R
  obtain ⟨hEy, hEz⟩ := extracted_le L w
  have hy := hEy.trans (Nat.mul_le_mul_right y (show Fintype.card C ≤
    Fintype.card A + Fintype.card B + Fintype.card C by omega))
  have hz := hEz.trans (Nat.mul_le_mul_right z (show Fintype.card B ≤
    Fintype.card A + Fintype.card B + Fintype.card C by omega))
  dsimp only at hh
  rw [← Nat.cast_mul, affine_residual_BC c t hy hz, Nat.cast_mul] at hh
  convert! hh using 1 <;> congr 1 <;> ring

theorem full_CA_affine (L : NNN12.BondLayout q d C A z x N) (w : Word q N)
    (φ : PolMul.Spectral ℂ) {c : Fin 3 → ℝ} (hb : AffineBound φ c)
    (t : ℝ) (ht : theta φ 1 ≤ t) (T : Tensor ℂ (X x) (X y) (X z))
    (P : Operator (BondAB A B (X x) (X y))) (Q : Operator (BondBC B C (X y) (X z))) :
    value φ (contract T P Q (L.kernel w)) ≤ (2 : ℝ) ^
      ((Fintype.card A + Fintype.card B + Fintype.card C : ℕ) * plane c ![(x : ℝ), y, z] +
        (d * (t - c 0 - c 2)) * weight w) := by
  have hh := L.full_CA_of_bound w φ hb t ht T P Q
  obtain ⟨hEz, hEx⟩ := extracted_le L w
  have hx := hEx.trans (Nat.mul_le_mul_right x (show Fintype.card C ≤
    Fintype.card A + Fintype.card B + Fintype.card C by omega))
  have hz := hEz.trans (Nat.mul_le_mul_right z (show Fintype.card A ≤
    Fintype.card A + Fintype.card B + Fintype.card C by omega))
  dsimp only at hh
  rw [← Nat.cast_mul, affine_residual_CA c t hx hz, Nat.cast_mul] at hh
  convert! hh using 1 <;> congr 1 <;> ring

/-- Retaining party A is enough for a labelled policy; the other orders can
use the corresponding extraction theorems without assuming spectral symmetry. -/
theorem retained_BC_affine (L : NNN12.BondLayout q d B C y z N) (w : Word q N)
    (φ : PolMul.Spectral ℂ) {c : Fin 3 → ℝ} (hb : AffineBound φ c)
    (t : ℝ) (ht : theta φ 0 ≤ t) (T : Tensor ℂ (X x) (X y) (X z)) :
    value φ (contract (A := A) T (identity _) (L.kernel w) (identity _)) ≤
      (2 : ℝ) ^ ((Fintype.card B + Fintype.card C : ℕ) * plane c ![(x : ℝ), y, z] +
        (d * (t - c 1 - c 2)) * weight w) * value φ T ^ Fintype.card A := by
  have hh := retained_BC_of_bound (A := A) L w φ hb t ht T
  obtain ⟨hEy, hEz⟩ := extracted_le L w
  have hy : d * weight w ≤ (Fintype.card B + Fintype.card C) * y :=
    hEy.trans (Nat.mul_le_mul_right y (Nat.le_add_left _ _))
  have hz : d * weight w ≤ (Fintype.card B + Fintype.card C) * z :=
    hEz.trans (Nat.mul_le_mul_right z (Nat.le_add_right _ _))
  dsimp only at hh
  rw [← Nat.cast_mul, affine_residual_BC c t hy hz, Nat.cast_mul] at hh
  convert! hh using 1 <;> congr 2 <;> ring

end OM.NNN13
