import Lib.OM.NNN12.Averaged

noncomputable section
open scoped BigOperators Classical
namespace OM.NNN12
open CoordinateTensor OM.NNN.Raw NNN11.Network
open NNN11 (bondLog)
open NNN11.ExtractionAB (X)
open Foundations.PairUnitExponents
set_option maxHeartbeats 1500000

theorem network28_raw_average (x y z : ℕ) (φ : PolMul.Spectral ℂ)
    (t : Fin 3 → ℝ) (hθ : ∀ i, theta φ i ≤ t i)
    (hs : t 0 + t 1 + t 2 = (9 : ℝ) / 4) (r : Fin 3 → ℕ)
    (hr : ∀ i, r i ≤ (![7 * min y z, 7 * min z x, 2 * min x y] : Fin 3 → ℕ) i)
    (T : Tensor ℂ (X x) (X y) (X z)) :
    value φ T ^ 28 ≤
      (2 : ℝ) ^ (∑ i, t i * ((bondLog 7 7 14 x y z i : ℝ) -
        r i * Real.logb 2 ((![3, 3, 7] : Fin 3 → ℕ) i))) +
      moment 3 (7 * min y z) (r 0) (28 * (t 2 * y + t 1 * z)) (1 * (2 * t 0 - 9 / 4)) +
      moment 3 (7 * min z x) (r 1) (28 * (t 2 * x + t 0 * z)) (1 * (2 * t 1 - 9 / 4)) +
      moment 7 (2 * min x y) (r 2) (14 * (t 1 * x + t 0 * y)) (2 * (2 * t 2 - 9 / 4)) *
        value φ T ^ 14 := by
  let q : Fin 3 → ℕ := ![3, 3, 7]
  let k : Fin 3 → ℕ := ![1, 1, 2]
  let N : Fin 3 → ℕ := ![7 * min y z, 7 * min z x, 2 * min x y]
  letI : ∀ i, Fact (q i).Prime := fun i => by fin_cases i <;> dsimp [q] <;> infer_instance
  have h := network_raw_average (q := q) (k := k) (N := N) (r := r)
    (Layouts.light28 x y) (Layouts.heavy28 y z) (Layouts.reverseHeavy28 z x) φ t hθ hs hr T
  simpa [q, k, N, starExponents] using! h

theorem network112_raw_average (x y z : ℕ) (φ : PolMul.Spectral ℂ)
    (t : Fin 3 → ℝ) (hθ : ∀ i, theta φ i ≤ t i)
    (hs : t 0 + t 1 + t 2 = (9 : ℝ) / 4) (r : Fin 3 → ℕ)
    (hr : ∀ i, r i ≤ (![7 * min y z, 7 * min z x, 10 * min x y] : Fin 3 → ℕ) i)
    (T : Tensor ℂ (X x) (X y) (X z)) :
    value φ T ^ 112 ≤
      (2 : ℝ) ^ (∑ i, t i * ((bondLog 35 35 42 x y z i : ℝ) -
        r i * Real.logb 2 ((![11, 11, 7] : Fin 3 → ℕ) i))) +
      moment 11 (7 * min y z) (r 0) (112 * (t 2 * y + t 1 * z)) (3 * (2 * t 0 - 9 / 4)) +
      moment 11 (7 * min z x) (r 1) (112 * (t 2 * x + t 0 * z)) (3 * (2 * t 1 - 9 / 4)) +
      moment 7 (10 * min x y) (r 2) (70 * (t 1 * x + t 0 * y)) (2 * (2 * t 2 - 9 / 4)) *
        value φ T ^ 42 := by
  let q : Fin 3 → ℕ := ![11, 11, 7]
  let k : Fin 3 → ℕ := ![3, 3, 2]
  let N : Fin 3 → ℕ := ![7 * min y z, 7 * min z x, 10 * min x y]
  letI : ∀ i, Fact (q i).Prime := fun i => by fin_cases i <;> dsimp [q] <;> infer_instance
  have h := network_raw_average (q := q) (k := k) (N := N) (r := r)
    (Layouts.light112 x y) (Layouts.heavy112 y z) (Layouts.reverseHeavy112 z x) φ t hθ hs hr T
  simpa [q, k, N, starExponents] using! h

theorem network196_raw_average (x y z : ℕ) (φ : PolMul.Spectral ℂ)
    (t : Fin 3 → ℝ) (hθ : ∀ i, theta φ i ≤ t i)
    (hs : t 0 + t 1 + t 2 = (9 : ℝ) / 4) (r : Fin 3 → ℕ)
    (hr : ∀ i, r i ≤ (![7 * min y z, 7 * min z x, 18 * min x y] : Fin 3 → ℕ) i)
    (T : Tensor ℂ (X x) (X y) (X z)) :
    value φ T ^ 196 ≤
      (2 : ℝ) ^ (∑ i, t i * ((bondLog 63 63 70 x y z i : ℝ) -
        r i * Real.logb 2 ((![19, 19, 7] : Fin 3 → ℕ) i))) +
      moment 19 (7 * min y z) (r 0) (196 * (t 2 * y + t 1 * z)) (5 * (2 * t 0 - 9 / 4)) +
      moment 19 (7 * min z x) (r 1) (196 * (t 2 * x + t 0 * z)) (5 * (2 * t 1 - 9 / 4)) +
      moment 7 (18 * min x y) (r 2) (126 * (t 1 * x + t 0 * y)) (2 * (2 * t 2 - 9 / 4)) *
        value φ T ^ 70 := by
  let q : Fin 3 → ℕ := ![19, 19, 7]
  let k : Fin 3 → ℕ := ![5, 5, 2]
  let N : Fin 3 → ℕ := ![7 * min y z, 7 * min z x, 18 * min x y]
  letI : ∀ i, Fact (q i).Prime := fun i => by fin_cases i <;> dsimp [q] <;> infer_instance
  have h := network_raw_average (q := q) (k := k) (N := N) (r := r)
    (Layouts.light196 x y) (Layouts.heavy196 y z) (Layouts.reverseHeavy196 z x) φ t hθ hs hr T
  simpa [q, k, N, starExponents] using! h

end OM.NNN12
