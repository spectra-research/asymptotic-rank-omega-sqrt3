import Lib.OM.NNN12.Excess

namespace P2M.R88

/-- The value function `F`: for a spectral point `φ` and a
real shape `y`, the supremum of `log₂ φ(W) / D` over `D ≥ 1` and dyadic tensors `W` (local
dimensions `2^{w_u}`) of log-format `w ≤ D y` coordinatewise, with `0` adjoined. -/
noncomputable def Fv (φ : OM.PolMul.Spectral ℂ) (y : Fin 3 → ℝ) : ℝ :=
  sSup (insert 0 {r | ∃ (D : ℕ) (w : OM.NNN12.Shape) (W : OM.NNN12.DyadicTensor w), 0 < D ∧
    (∀ i, (w i : ℝ) ≤ D * y i) ∧ 0 < OM.NNN.Raw.value φ W ∧
    r = Real.logb 2 (OM.NNN.Raw.value φ W) / D})

end P2M.R88
