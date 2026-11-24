import Lib.OM.NNN11.CodePrice

/-! Uniform word prices and the exact compressed head exponent. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN11
open CoordinateTensor OM.NNN.Raw OM.NNN2 Network
open ExtractionAB (X)
open Foundations.PairUnitExponents
set_option maxHeartbeats 1500000

def wordPrice {N : ℕ} (d : ℕ) (S t : ℝ) (c : Word N) : ℝ :=
  (2 : ℝ) ^ ((d : ℝ) * S + (4 * t - 9 / 2) * weight c)

namespace BondLayout
variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C]
  {x y z N : ℕ}

theorem full_AB (L : BondLayout A B x y N) (c : Word N)
    (φ : PolMul.Spectral ℂ) (t : Fin 3 → ℝ) (ht : ∀ i, theta φ i ≤ t i)
    (hs : t 0 + t 1 + t 2 = (9 : ℝ) / 4) (T : Tensor ℂ (X x) (X y) (X z))
    (Q : Operator (BondBC B C (X y) (X z))) (R : Operator (BondCA C A (X z) (X x))) :
    value φ (contract T (L.kernel c) Q R) ≤
      wordPrice (Fintype.card A + Fintype.card B + Fintype.card C) (t 1 * x + t 0 * y) (t 2) c := by
  have h := ExtractionAB.permutation_network_star_enlarged
    (MixedCrossings.permutation L.coordinates c) (MixedCrossings.active L.coordinates c)
    (MixedCrossings.stable L.coordinates c) (MixedCrossings.fixed L.coordinates c) φ t ht hs T Q R
  rw [L.crossings] at h
  apply (value_le_change_fintypes φ _ h).trans_eq
  dsimp [wordPrice]
  push_cast
  congr 1
  ring

theorem retained_AB (L : BondLayout A B x y N) (c : Word N)
    (φ : PolMul.Spectral ℂ) (t : Fin 3 → ℝ) (ht : ∀ i, theta φ i ≤ t i)
    (hs : t 0 + t 1 + t 2 = (9 : ℝ) / 4) (T : Tensor ℂ (X x) (X y) (X z)) :
    value φ (contract (C := C) T (L.kernel c) (Network.identity _) (Network.identity _)) ≤
      wordPrice (Fintype.card A + Fintype.card B) (t 1 * x + t 0 * y) (t 2) c * value φ T ^ Fintype.card C := by
  have h := ExtractionAB.retained_star_enlarged (C := C)
    (MixedCrossings.permutation L.coordinates c) (MixedCrossings.active L.coordinates c)
    (MixedCrossings.stable L.coordinates c) (MixedCrossings.fixed L.coordinates c) φ t ht hs T
  rw [L.crossings] at h
  apply (value_le_change_fintypes φ _ h).trans_eq
  dsimp [wordPrice]
  push_cast
  congr 2
  ring

theorem full_BC (L : BondLayout B C y z N) (c : Word N)
    (φ : PolMul.Spectral ℂ) (t : Fin 3 → ℝ) (ht : ∀ i, theta φ i ≤ t i)
    (hs : t 0 + t 1 + t 2 = (9 : ℝ) / 4) (T : Tensor ℂ (X x) (X y) (X z))
    (P : Operator (BondAB A B (X x) (X y))) (R : Operator (BondCA C A (X z) (X x))) :
    value φ (contract T P (L.kernel c) R) ≤
      wordPrice (Fintype.card A + Fintype.card B + Fintype.card C) (t 2 * y + t 1 * z) (t 0) c := by
  have h := ExtractionBC.permutation_network_star_enlarged
    (MixedCrossings.permutation L.coordinates c) (MixedCrossings.active L.coordinates c)
    (MixedCrossings.stable L.coordinates c) (MixedCrossings.fixed L.coordinates c) φ t ht hs T P R
  rw [L.crossings] at h
  apply (value_le_change_fintypes φ _ h).trans_eq
  dsimp [wordPrice]
  push_cast
  congr 1
  ring

theorem retained_BC (L : BondLayout B C y z N) (c : Word N)
    (φ : PolMul.Spectral ℂ) (t : Fin 3 → ℝ) (ht : ∀ i, theta φ i ≤ t i)
    (hs : t 0 + t 1 + t 2 = (9 : ℝ) / 4) (T : Tensor ℂ (X x) (X y) (X z)) :
    value φ (contract (A := A) T (Network.identity _) (L.kernel c) (Network.identity _)) ≤
      wordPrice (Fintype.card B + Fintype.card C) (t 2 * y + t 1 * z) (t 0) c * value φ T ^ Fintype.card A := by
  have h := ExtractionBC.retained_star_enlarged (A := A)
    (MixedCrossings.permutation L.coordinates c) (MixedCrossings.active L.coordinates c)
    (MixedCrossings.stable L.coordinates c) (MixedCrossings.fixed L.coordinates c) φ t ht hs T
  rw [L.crossings] at h
  apply (value_le_change_fintypes φ _ h).trans_eq
  dsimp [wordPrice]
  push_cast
  congr 2
  ring

theorem full_CA (L : BondLayout C A z x N) (c : Word N)
    (φ : PolMul.Spectral ℂ) (t : Fin 3 → ℝ) (ht : ∀ i, theta φ i ≤ t i)
    (hs : t 0 + t 1 + t 2 = (9 : ℝ) / 4) (T : Tensor ℂ (X x) (X y) (X z))
    (P : Operator (BondAB A B (X x) (X y))) (Q : Operator (BondBC B C (X y) (X z))) :
    value φ (contract T P Q (L.kernel c)) ≤
      wordPrice (Fintype.card A + Fintype.card B + Fintype.card C) (t 2 * x + t 0 * z) (t 1) c := by
  have h := ExtractionCA.permutation_network_star_enlarged
    (MixedCrossings.permutation L.coordinates c) (MixedCrossings.active L.coordinates c)
    (MixedCrossings.stable L.coordinates c) (MixedCrossings.fixed L.coordinates c) φ t ht hs T P Q
  rw [L.crossings] at h
  apply (value_le_change_fintypes φ _ h).trans_eq
  dsimp [wordPrice]
  push_cast
  congr 1
  ring

theorem retained_CA (L : BondLayout C A z x N) (c : Word N)
    (φ : PolMul.Spectral ℂ) (t : Fin 3 → ℝ) (ht : ∀ i, theta φ i ≤ t i)
    (hs : t 0 + t 1 + t 2 = (9 : ℝ) / 4) (T : Tensor ℂ (X x) (X y) (X z)) :
    value φ (contract (B := B) T (Network.identity _) (Network.identity _) (L.kernel c)) ≤
      wordPrice (Fintype.card A + Fintype.card C) (t 2 * x + t 0 * z) (t 1) c * value φ T ^ Fintype.card B := by
  have h := ExtractionCA.retained_star_enlarged (B := B)
    (MixedCrossings.permutation L.coordinates c) (MixedCrossings.active L.coordinates c)
    (MixedCrossings.stable L.coordinates c) (MixedCrossings.fixed L.coordinates c) φ t ht hs T
  rw [L.crossings] at h
  apply (value_le_change_fintypes φ _ h).trans_eq
  dsimp [wordPrice]
  push_cast
  congr 2
  ring

end BondLayout

lemma seven_rpow_logb : (2 : ℝ) ^ Real.logb 2 7 = 7 :=
  Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)

lemma headPrice_eq (a b c x y z : ℕ) (r : Fin 3 → ℕ) (t : Fin 3 → ℝ) :
    headPrice a b c x y z r t =
      (2 : ℝ) ^ (∑ i, t i * ((bondLog a b c x y z i : ℝ) - r i * Real.logb 2 7)) := by
  rw [headPrice, Real.rpow_sum_of_pos (by norm_num)]
  apply Finset.prod_congr rfl
  intro i _
  have h7 : (7 : ℝ) ^ r i = (2 : ℝ) ^ ((r i : ℝ) * Real.logb 2 7) := by
    rw [mul_comm, Real.rpow_mul (by norm_num), seven_rpow_logb, Real.rpow_natCast]
  rw [h7, ← Real.rpow_natCast, ← Real.rpow_sub (by norm_num),
    ← Real.rpow_mul (by norm_num)]
  congr 1
  ring

theorem headPrice_enlarge {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    {x y z : ℕ} {N r : Fin 3 → ℕ}
    (Lab : BondLayout A B x y (N 2)) (Lbc : BondLayout B C y z (N 0))
    (Lca : BondLayout C A z x (N 1)) (hr : ∀ i, r i ≤ N i)
    (φ : PolMul.Spectral ℂ) (t : Fin 3 → ℝ) (ht : ∀ i, theta φ i ≤ t i) :
    headPrice (Fintype.card A) (Fintype.card B) (Fintype.card C) x y z r (theta φ) ≤
      (2 : ℝ) ^ (∑ i, t i * ((bondLog (Fintype.card A) (Fintype.card B) (Fintype.card C) x y z i : ℝ) -
        r i * Real.logb 2 7)) := by
  rw [← headPrice_eq]
  apply Finset.prod_le_prod₀
  · intro i _
    positivity
  · intro i _
    apply Real.rpow_le_rpow_of_exponent_le _ (ht i)
    fin_cases i
    · exact Lbc.head_base_ge_one (hr 0)
    · exact Lca.head_base_ge_one (hr 1)
    · exact Lab.head_base_ge_one (hr 2)

end OM.NNN11
