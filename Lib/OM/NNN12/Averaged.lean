import Lib.OM.NNN12.CodePrice
import Lib.OM.NNN12.Moments

/-! A finite raw-price inequality for every mixed-alphabet layout, with the
actual retained input factor. This is the common starting point for the raw
112-copy helper and the retained groups of the other networks. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN12
open CoordinateTensor OM.NNN.Raw NNN11.Network
open NNN11 (bondLog)
open NNN11.ExtractionAB (X)
open Foundations.PairUnitExponents Codes
set_option maxHeartbeats 2000000

def starExponents (x y z : ℕ) (t : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![t 2 * y + t 1 * z, t 2 * x + t 0 * z, t 1 * x + t 0 * y]

theorem network_raw_average {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    {x y z : ℕ} {N r q k : Fin 3 → ℕ} [∀ i, Fact (q i).Prime]
    (Lab : BondLayout (q 2) (k 2) A B x y (N 2)) (Lbc : BondLayout (q 0) (k 0) B C y z (N 0))
    (Lca : BondLayout (q 1) (k 1) C A z x (N 1))
    (φ : PolMul.Spectral ℂ) (t : Fin 3 → ℝ) (hθ : ∀ i, theta φ i ≤ t i)
    (hs : t 0 + t 1 + t 2 = (9 : ℝ) / 4) (hr : ∀ i, r i ≤ N i)
    (T : Tensor ℂ (X x) (X y) (X z)) :
    let p := Fintype.card A + Fintype.card B + Fintype.card C
    let m := Fintype.card A + Fintype.card B
    let S := starExponents x y z t
    let D := fun i => (k i : ℝ) * (2 * t i - 9 / 4)
    value φ T ^ p ≤
      (2 : ℝ) ^ (∑ i, t i * ((bondLog (Fintype.card A) (Fintype.card B) (Fintype.card C) x y z i : ℝ) -
        r i * Real.logb 2 (q i))) +
      moment (q 0) (N 0) (r 0) (p * S 0) (D 0) +
      moment (q 1) (N 1) (r 1) (p * S 1) (D 1) +
      moment (q 2) (N 2) (r 2) (m * S 2) (D 2) * value φ T ^ Fintype.card C := by
  dsimp only
  let d (i : Fin 3) := if i = 2 then Fintype.card A + Fintype.card B
    else Fintype.card A + Fintype.card B + Fintype.card C
  let a (i : Fin 3) : ℝ := d i * starExponents x y z t i
  let D (i : Fin 3) : ℝ := k i * (2 * t i - 9 / 4)
  choose code hcode using (fun i => exists_generator_price (q := q i) (N i) (r i) (a i) (D i))
  let cost (i : Fin 3) (c : Word (q i) (N i)) := (2 : ℝ) ^ (a i + D i * weight c) *
    (if i = 2 then value φ T ^ Fintype.card C else 1)
  have hab (c : Word (q 2) (N 2)) :
      value φ (contract (C := C) T (Lab.kernel c) (identity _) (identity _)) ≤ cost 2 c := by
    simpa [cost, a, D, d, starExponents, wordPrice] using! Lab.retained_AB (C := C) c φ t hθ hs T
  have hbc (c : Word (q 0) (N 0)) P R :
      value φ (contract (A := A) T P (Lbc.kernel c) R) ≤ cost 0 c := by
    simpa [cost, a, D, d, starExponents, wordPrice] using! Lbc.full_BC (A := A) c φ t hθ hs T P R
  have hca (c : Word (q 1) (N 1)) P Q :
      value φ (contract (B := B) T P Q (Lca.kernel c)) ≤ cost 1 c := by
    simpa [cost, a, D, d, starExponents, wordPrice] using! Lca.full_CA (B := B) c φ t hθ hs T P Q
  have h := network_code_price φ T Lab Lbc Lca code cost hab hbc hca
  have hh := headPrice_enlarge Lab Lbc Lca hr φ t hθ
  have h0 := hcode 0
  have h1 := hcode 1
  have h2 := mul_le_mul_of_nonneg_right (hcode 2)
    (show 0 ≤ value φ T ^ Fintype.card C from pow_nonneg (φ.nonneg _) _)
  simp only [cost, show ¬(0 : Fin 3) = 2 by decide +kernel,
    show ¬(1 : Fin 3) = 2 by decide +kernel, if_false, if_true, mul_one, ← Finset.sum_mul] at h
  dsimp [a, D, d] at h0 h1 h2
  exact h.trans (add_le_add (add_le_add (add_le_add hh h0) h1) h2)

end OM.NNN12
