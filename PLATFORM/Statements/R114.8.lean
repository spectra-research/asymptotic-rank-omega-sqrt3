import Foundations.Tensors.Semicontinuity.MaxRankBound
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

namespace P2M.R114

noncomputable def pivotColumns {D : ℕ+} (R : Semicontinuity.KTensor ℂ (fun _ : Fin 4 => D)) :
    List (Fin (D : ℕ) × Fin (D : ℕ)) := by
  classical
  let col (j : Fin ((D : ℕ) * (D : ℕ))) (ab : Fin (D : ℕ) × Fin (D : ℕ)) :=
    let ce : Fin (D : ℕ) × Fin (D : ℕ) := finProdFinEquiv.symm j
    R ![ab.1, ab.2, ce.2, ce.1]
  let pivots := (List.finRange ((D : ℕ) * (D : ℕ))).filter fun j =>
    decide (col j ∉ Submodule.span ℂ (col '' Set.Iio j))
  exact pivots.map finProdFinEquiv.symm

end P2M.R114
