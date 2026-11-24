import Lib.OM.NNN12.Layout
import Lib.OM.NNN11.LayoutPrices

/-! Exact raw correction prices at the original spectral point, for each
physical bond and each prime alphabet. The existing NNN11 extraction and
retention theorems supply the actual restrictions with arbitrary complements. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN12
open CoordinateTensor OM.NNN.Raw OM.NNN2 NNN11.Network
open NNN11 (value_le_change_fintypes)
open NNN11.ExtractionAB (X)
open Foundations.PairUnitExponents Codes
set_option maxHeartbeats 1500000

def wordPrice {q N : ℕ} [Fact q.Prime] (k d : ℕ) (S t : ℝ) (c : Word q N) : ℝ :=
  (2 : ℝ) ^ ((d : ℝ) * S + ((k : ℝ) * (2 * t - 9 / 4)) * weight c)

namespace BondLayout
variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C]
  {q k x y z N : ℕ} [Fact q.Prime]

theorem full_AB (L : BondLayout q k A B x y N) (c : Word q N)
    (φ : PolMul.Spectral ℂ) (t : Fin 3 → ℝ) (ht : ∀ i, theta φ i ≤ t i)
    (hs : t 0 + t 1 + t 2 = (9 : ℝ) / 4) (T : Tensor ℂ (X x) (X y) (X z))
    (Q : Operator (BondBC B C (X y) (X z))) (R : Operator (BondCA C A (X z) (X x))) :
    value φ (contract T (L.kernel c) Q R) ≤
      wordPrice k (Fintype.card A + Fintype.card B + Fintype.card C) (t 1 * x + t 0 * y) (t 2) c := by
  have h := NNN11.ExtractionAB.permutation_network_star_enlarged
    (Cyclic.permutation L.coordinates c) (Cyclic.active L.coordinates c)
    (Cyclic.stable L.coordinates c) (Cyclic.fixed L.coordinates c) φ t ht hs T Q R
  rw [L.crossings] at h
  apply (value_le_change_fintypes φ _ h).trans_eq
  dsimp [wordPrice]
  push_cast
  congr 1
  ring

theorem retained_AB (L : BondLayout q k A B x y N) (c : Word q N)
    (φ : PolMul.Spectral ℂ) (t : Fin 3 → ℝ) (ht : ∀ i, theta φ i ≤ t i)
    (hs : t 0 + t 1 + t 2 = (9 : ℝ) / 4) (T : Tensor ℂ (X x) (X y) (X z)) :
    value φ (contract (C := C) T (L.kernel c) (NNN11.Network.identity _) (NNN11.Network.identity _)) ≤
      wordPrice k (Fintype.card A + Fintype.card B) (t 1 * x + t 0 * y) (t 2) c * value φ T ^ Fintype.card C := by
  have h := NNN11.ExtractionAB.retained_star_enlarged (C := C)
    (Cyclic.permutation L.coordinates c) (Cyclic.active L.coordinates c)
    (Cyclic.stable L.coordinates c) (Cyclic.fixed L.coordinates c) φ t ht hs T
  rw [L.crossings] at h
  apply (value_le_change_fintypes φ _ h).trans_eq
  dsimp [wordPrice]
  push_cast
  congr 2
  ring

theorem full_BC (L : BondLayout q k B C y z N) (c : Word q N)
    (φ : PolMul.Spectral ℂ) (t : Fin 3 → ℝ) (ht : ∀ i, theta φ i ≤ t i)
    (hs : t 0 + t 1 + t 2 = (9 : ℝ) / 4) (T : Tensor ℂ (X x) (X y) (X z))
    (P : Operator (BondAB A B (X x) (X y))) (R : Operator (BondCA C A (X z) (X x))) :
    value φ (contract T P (L.kernel c) R) ≤
      wordPrice k (Fintype.card A + Fintype.card B + Fintype.card C) (t 2 * y + t 1 * z) (t 0) c := by
  have h := NNN11.ExtractionBC.permutation_network_star_enlarged
    (Cyclic.permutation L.coordinates c) (Cyclic.active L.coordinates c)
    (Cyclic.stable L.coordinates c) (Cyclic.fixed L.coordinates c) φ t ht hs T P R
  rw [L.crossings] at h
  apply (value_le_change_fintypes φ _ h).trans_eq
  dsimp [wordPrice]
  push_cast
  congr 1
  ring

theorem retained_BC (L : BondLayout q k B C y z N) (c : Word q N)
    (φ : PolMul.Spectral ℂ) (t : Fin 3 → ℝ) (ht : ∀ i, theta φ i ≤ t i)
    (hs : t 0 + t 1 + t 2 = (9 : ℝ) / 4) (T : Tensor ℂ (X x) (X y) (X z)) :
    value φ (contract (A := A) T (NNN11.Network.identity _) (L.kernel c) (NNN11.Network.identity _)) ≤
      wordPrice k (Fintype.card B + Fintype.card C) (t 2 * y + t 1 * z) (t 0) c * value φ T ^ Fintype.card A := by
  have h := NNN11.ExtractionBC.retained_star_enlarged (A := A)
    (Cyclic.permutation L.coordinates c) (Cyclic.active L.coordinates c)
    (Cyclic.stable L.coordinates c) (Cyclic.fixed L.coordinates c) φ t ht hs T
  rw [L.crossings] at h
  apply (value_le_change_fintypes φ _ h).trans_eq
  dsimp [wordPrice]
  push_cast
  congr 2
  ring

theorem full_CA (L : BondLayout q k C A z x N) (c : Word q N)
    (φ : PolMul.Spectral ℂ) (t : Fin 3 → ℝ) (ht : ∀ i, theta φ i ≤ t i)
    (hs : t 0 + t 1 + t 2 = (9 : ℝ) / 4) (T : Tensor ℂ (X x) (X y) (X z))
    (P : Operator (BondAB A B (X x) (X y))) (Q : Operator (BondBC B C (X y) (X z))) :
    value φ (contract T P Q (L.kernel c)) ≤
      wordPrice k (Fintype.card A + Fintype.card B + Fintype.card C) (t 2 * x + t 0 * z) (t 1) c := by
  have h := NNN11.ExtractionCA.permutation_network_star_enlarged
    (Cyclic.permutation L.coordinates c) (Cyclic.active L.coordinates c)
    (Cyclic.stable L.coordinates c) (Cyclic.fixed L.coordinates c) φ t ht hs T P Q
  rw [L.crossings] at h
  apply (value_le_change_fintypes φ _ h).trans_eq
  dsimp [wordPrice]
  push_cast
  congr 1
  ring

theorem retained_CA (L : BondLayout q k C A z x N) (c : Word q N)
    (φ : PolMul.Spectral ℂ) (t : Fin 3 → ℝ) (ht : ∀ i, theta φ i ≤ t i)
    (hs : t 0 + t 1 + t 2 = (9 : ℝ) / 4) (T : Tensor ℂ (X x) (X y) (X z)) :
    value φ (contract (B := B) T (NNN11.Network.identity _) (NNN11.Network.identity _) (L.kernel c)) ≤
      wordPrice k (Fintype.card A + Fintype.card C) (t 2 * x + t 0 * z) (t 1) c * value φ T ^ Fintype.card B := by
  have h := NNN11.ExtractionCA.retained_star_enlarged (B := B)
    (Cyclic.permutation L.coordinates c) (Cyclic.active L.coordinates c)
    (Cyclic.stable L.coordinates c) (Cyclic.fixed L.coordinates c) φ t ht hs T
  rw [L.crossings] at h
  apply (value_le_change_fintypes φ _ h).trans_eq
  dsimp [wordPrice]
  push_cast
  congr 2
  ring

end BondLayout

end OM.NNN12
