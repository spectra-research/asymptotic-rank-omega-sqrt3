import PLATFORM.Statements.«R114.9»

namespace P2M.R114

noncomputable def rightFactor (H : ℕ) : Semicontinuity.KTensor ℂ (fun _ : Fin 3 => partitionSide H) := by
  classical
  let D := (partitionSide H : ℕ)
  let r := (pivotColumns (rowPiece H)).length
  intro a
  let coords (v : Fin D → ℂ) : Prop :=
    (∀ j : Fin D, r ≤ j.val → v j = 0) ∧
    ∀ i b : Fin D, rowPiece H ![i, b, a 1, a 0] = ∑ j, leftFactor H ![i, b, j] * v j
  exact if h : ∃! v, coords v then (Classical.choose h) (a 2) else 0

end P2M.R114
