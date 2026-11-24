import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Basic.Complex.Basic

/-- The rectangular crossing estimate, at widths `a = α/q`, `b = β/q` and scales
`L = q j`.  For each `j` the product of the equality on `z, ∞` (size `2^(La) = 2^(α j)`) and the
equality on `0, 1` (size `2^(Lb) = 2^(β j)`) is the sum of the `K j = O(L²)` pieces `B j k`; for
every `ε > 0`, eventually in `j`, every nonzero piece has `r² + c² ≤ 2(a² + b²) + ε`, where `r, c`
are `log₂` of its ranks across `z0 | 1∞` and `z1 | 0∞`, divided by `L`. -/
def S_R108_3 : Prop :=
  ∀ α β q : ℕ, 0 < α → 0 < β → 0 < q →
    ∃ (K : ℕ → ℕ) (B : (j : ℕ) → Fin (K j) →
        Fin (2 ^ (α * j)) → Fin (2 ^ (β * j)) → Fin (2 ^ (β * j)) → Fin (2 ^ (α * j)) → ℂ),
      (∃ C : ℝ, ∀ j : ℕ, (K j : ℝ) ≤ C * ((q * j : ℕ) + 1 : ℝ) ^ 2) ∧
      (∀ j z x y w, ∑ k, B j k z x y w = if z = w ∧ x = y then 1 else 0) ∧
      ∀ ε : ℝ, 0 < ε → ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j → ∀ k : Fin (K j), B j k ≠ 0 →
        (Real.logb 2 (Matrix.of fun (zx : Fin (2 ^ (α * j)) × Fin (2 ^ (β * j)))
              (yw : Fin (2 ^ (β * j)) × Fin (2 ^ (α * j))) => B j k zx.1 zx.2 yw.1 yw.2).rank /
            (q * j : ℕ)) ^ 2 +
        (Real.logb 2 (Matrix.of fun (zy : Fin (2 ^ (α * j)) × Fin (2 ^ (β * j)))
              (xw : Fin (2 ^ (β * j)) × Fin (2 ^ (α * j))) => B j k zy.1 xw.1 zy.2 xw.2).rank /
            (q * j : ℕ)) ^ 2
          ≤ 2 * (((α : ℝ) / q) ^ 2 + ((β : ℝ) / q) ^ 2) + ε
