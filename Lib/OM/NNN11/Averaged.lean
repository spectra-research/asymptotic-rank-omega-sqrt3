import Lib.OM.NNN11.LayoutPrices
import Lib.OM.NNN11.Moments

/-! All three generator averages at one spectral point. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN11
open CoordinateTensor OM.NNN.Raw OM.NNN2 Network
open ExtractionAB (X)
open Foundations.PairUnitExponents
set_option maxHeartbeats 2000000

def sourceLog (x y z : ℕ) (t : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![t 2 * y + t 1 * z, t 2 * x + t 0 * z, t 1 * x + t 0 * y]

theorem network_raw_average {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    {x y z : ℕ} {N r : Fin 3 → ℕ}
    (Lab : BondLayout A B x y (N 2)) (Lbc : BondLayout B C y z (N 0))
    (Lca : BondLayout C A z x (N 1)) (hr : ∀ i, r i ≤ N i)
    (φ : PolMul.Spectral ℂ) (t : Fin 3 → ℝ) (ht : ∀ i, theta φ i ≤ t i)
    (hs : t 0 + t 1 + t 2 = (9 : ℝ) / 4) (T : Tensor ℂ (X x) (X y) (X z)) :
    value φ T ^ (Fintype.card A + Fintype.card B + Fintype.card C) ≤
      (2 : ℝ) ^ (∑ i, t i * ((bondLog (Fintype.card A) (Fintype.card B) (Fintype.card C) x y z i : ℝ) -
        r i * Real.logb 2 7)) +
      moment (N 0) (r 0) ((Fintype.card A + Fintype.card B + Fintype.card C : ℕ) * sourceLog x y z t 0) (4 * t 0 - 9 / 2) +
      moment (N 1) (r 1) ((Fintype.card A + Fintype.card B + Fintype.card C : ℕ) * sourceLog x y z t 1) (4 * t 1 - 9 / 2) +
      moment (N 2) (r 2) ((Fintype.card A + Fintype.card B : ℕ) * sourceLog x y z t 2) (4 * t 2 - 9 / 2) *
        value φ T ^ Fintype.card C := by
  let d : Fin 3 → ℕ := ![Fintype.card A + Fintype.card B + Fintype.card C,
    Fintype.card A + Fintype.card B + Fintype.card C, Fintype.card A + Fintype.card B]
  choose code hcode using (fun i => exists_generator_price (N i) (r i)
    ((d i : ℝ) * sourceLog x y z t i) (4 * t i - 9 / 2))
  let p (i : Fin 3) (c : Word (N i)) := wordPrice (d i) (sourceLog x y z t i) (t i) c *
    (if i = 2 then value φ T ^ Fintype.card C else 1)
  have ha (c : Word (N 2)) : value φ (contract (C := C) T (Lab.kernel c) (Network.identity _) (Network.identity _)) ≤ p 2 c := by
    exact Lab.retained_AB c φ t ht hs T
  have hb (c : Word (N 0)) P R : value φ (contract (A := A) T P (Lbc.kernel c) R) ≤ p 0 c := by
    simpa only [p, d, sourceLog, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      show ¬(0 : Fin 3) = 2 by decide +kernel, if_false, mul_one] using! Lbc.full_BC c φ t ht hs T P R
  have hc (c : Word (N 1)) P Q : value φ (contract (B := B) T P Q (Lca.kernel c)) ≤ p 1 c := by
    simpa only [p, d, sourceLog, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      show ¬(1 : Fin 3) = 2 by decide +kernel, if_false, mul_one] using! Lca.full_CA c φ t ht hs T P Q
  have h := network_code_price φ T Lab Lbc Lca code p ha hb hc
  have hm := headPrice_enlarge Lab Lbc Lca hr φ t ht
  have h0 := hcode 0
  have h1 := hcode 1
  have h2 := mul_le_mul_of_nonneg_right (hcode 2)
    (show 0 ≤ value φ T ^ Fintype.card C from pow_nonneg (φ.nonneg _) _)
  simp only [p, d, sourceLog, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    show ¬(0 : Fin 3) = 2 by decide +kernel, show ¬(1 : Fin 3) = 2 by decide +kernel,
    if_false, if_true, mul_one, ← Finset.sum_mul, wordPrice] at h
  simp only [d, sourceLog, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at h0 h1 h2 ⊢
  simp only [Matrix.head_cons, Matrix.tail_cons] at h h0 h1 h2 ⊢
  linarith only [h, hm, h0, h1, h2]

theorem network70_raw_average {x y z : ℕ} (φ : PolMul.Spectral ℂ)
    (t : Fin 3 → ℝ) (ht : ∀ i, theta φ i ≤ t i) (hs : t 0 + t 1 + t 2 = (9 : ℝ) / 4)
    (r : Fin 3 → ℕ)
    (h0 : r 0 ≤ 7 * min y z) (h1 : r 1 ≤ 7 * min z x) (h2 : r 2 ≤ 6 * min x y)
    (T : Tensor ℂ (X x) (X y) (X z)) :
    value φ T ^ 70 ≤
      (2 : ℝ) ^ (∑ i, t i * ((bondLog 21 21 28 x y z i : ℝ) - r i * Real.logb 2 7)) +
      moment (7 * min y z) (r 0) (70 * sourceLog x y z t 0) (4 * t 0 - 9 / 2) +
      moment (7 * min z x) (r 1) (70 * sourceLog x y z t 1) (4 * t 1 - 9 / 2) +
      moment (6 * min x y) (r 2) (42 * sourceLog x y z t 2) (4 * t 2 - 9 / 2) * value φ T ^ 28 := by
  have h := network_raw_average (N := ![7 * min y z, 7 * min z x, 6 * min x y]) (r := r)
    (BondCoordinates.light x y) (BondCoordinates.heavy y z) (BondCoordinates.reverseHeavy z x)
    (by intro i; fin_cases i; exact h0; exact h1; exact h2) φ t ht hs T
  simp only [Fintype.card_fin, Nat.cast_ofNat] at h
  exact h

end OM.NNN11
