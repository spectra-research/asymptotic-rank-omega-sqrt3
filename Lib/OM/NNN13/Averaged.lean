import Lib.OM.NNN13.AffineExtraction
import Lib.OM.NNN12.TelescopeA
import Lib.OM.NNN12.Moments

/-! A finite combined recursive network inequality, for arbitrary ownership
counts, mixed-alphabet layouts, and affine residual majorants. All three
groups are priced recursively; party A's untouched copies retain their
actual spectral value. Integer cycle and code dimensions remain explicit. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN13
open CoordinateTensor OM.NNN.Raw NNN11.Network
open NNN11 (bondLog)
open NNN11.ExtractionAB (X)
open Foundations.PairUnitExponents NNN12.Codes
set_option maxHeartbeats 2000000

variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C]
  {x y z : ℕ} {N r q d : Fin 3 → ℕ} [∀ i, Fact (q i).Prime]

theorem combined_network_average (φ : PolMul.Spectral ℂ)
    (c : Fin 3 → Fin 3 → ℝ) (hb : ∀ i, AffineBound φ (c i))
    (t : Fin 3 → ℝ) (hθ : ∀ i, theta φ i ≤ t i)
    (Lab : NNN12.BondLayout (q 2) (d 2) A B x y (N 2))
    (Lbc : NNN12.BondLayout (q 0) (d 0) B C y z (N 0))
    (Lca : NNN12.BondLayout (q 1) (d 1) C A z x (N 1))
    (hr : ∀ i, r i ≤ N i) (T : Tensor ℂ (X x) (X y) (X z)) :
    let p := Fintype.card A + Fintype.card B + Fintype.card C
    let m := Fintype.card B + Fintype.card C
    let v : Fin 3 → ℝ := ![x, y, z]
    value φ T ^ p ≤
      (2 : ℝ) ^ (∑ i, t i * ((bondLog (Fintype.card A) (Fintype.card B)
        (Fintype.card C) x y z i : ℝ) - r i * Real.logb 2 (q i))) +
      NNN12.moment (q 0) (N 0) (r 0) (m * plane (c 0) v)
        (d 0 * (t 0 - c 0 1 - c 0 2)) * value φ T ^ Fintype.card A +
      NNN12.moment (q 1) (N 1) (r 1) (p * plane (c 1) v)
        (d 1 * (t 1 - c 1 0 - c 1 2)) +
      NNN12.moment (q 2) (N 2) (r 2) (p * plane (c 2) v)
        (d 2 * (t 2 - c 2 0 - c 2 1)) := by
  dsimp only
  let p := Fintype.card A + Fintype.card B + Fintype.card C
  let m := Fintype.card B + Fintype.card C
  let v : Fin 3 → ℝ := ![x, y, z]
  let M : Fin 3 → ℝ := ![m * plane (c 0) v, p * plane (c 1) v, p * plane (c 2) v]
  let D : Fin 3 → ℝ := ![d 0 * (t 0 - c 0 1 - c 0 2),
    d 1 * (t 1 - c 1 0 - c 1 2), d 2 * (t 2 - c 2 0 - c 2 1)]
  choose code hc using fun i : Fin 3 =>
    NNN12.exists_generator_price (q := q i) (N i) (r i) (M i) (D i)
  let cost : (i : Fin 3) → Word (q i) (N i) → ℝ :=
    Fin.cases (fun w => (2 : ℝ) ^ (M 0 + D 0 * weight w) * value φ T ^ Fintype.card A)
      (Fin.cases (fun w => (2 : ℝ) ^ (M 1 + D 1 * weight w))
        (Fin.cases (fun w => (2 : ℝ) ^ (M 2 + D 2 * weight w))
          (fun i => Fin.elim0 i)))
  have hab w Q R : value φ (contract (C := C) T (Lab.kernel w) Q R) ≤ cost 2 w :=
    full_AB_affine Lab w φ (hb 2) (t 2) (hθ 2) T Q R
  have hbc w : value φ (contract (A := A) T (identity _) (Lbc.kernel w) (identity _)) ≤ cost 0 w :=
    retained_BC_affine Lbc w φ (hb 0) (t 0) (hθ 0) T
  have hca w P Q : value φ (contract (B := B) T P Q (Lca.kernel w)) ≤ cost 1 w :=
    full_CA_affine Lca w φ (hb 1) (t 1) (hθ 1) T P Q
  have hh := NNN12.network_code_price_lastBC φ T Lab Lbc Lca code cost hab hbc hca
  have hhead := NNN12.headPrice_enlarge Lab Lbc Lca hr φ t hθ
  have hc0 := mul_le_mul_of_nonneg_right (hc 0)
    (show 0 ≤ value φ T ^ Fintype.card A from pow_nonneg (φ.nonneg _) _)
  have hc1 := hc 1
  have hc2 := hc 2
  change value φ T ^ p ≤
    NNN12.headPrice q (Fintype.card A) (Fintype.card B) (Fintype.card C) x y z r (theta φ) +
      (∑ w ∈ Finset.univ.erase (0 : Word (q 0) (r 0)),
        (2 : ℝ) ^ (M 0 + D 0 * weight (code 0 w)) * value φ T ^ Fintype.card A) +
      (∑ w ∈ Finset.univ.erase (0 : Word (q 1) (r 1)),
        (2 : ℝ) ^ (M 1 + D 1 * weight (code 1 w))) +
      (∑ w ∈ Finset.univ.erase (0 : Word (q 2) (r 2)),
        (2 : ℝ) ^ (M 2 + D 2 * weight (code 2 w))) at hh
  rw [← Finset.sum_mul] at hh
  dsimp [M, D, p, m, v] at hc0 hc1 hc2 hh
  linarith only [hh, hhead, hc0, hc1, hc2]

end OM.NNN13
